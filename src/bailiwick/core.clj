(ns bailiwick.core
  (:require [clojure.math :as math]
            [clojure.core.match :refer [match]]
            [clojure.walk :as walk]
            [instaparse.core :as insta])
  (:import (java.math RoundingMode)
           (java.time LocalDate LocalTime)
           (java.time.format DateTimeFormatter)))

(set! *warn-on-reflection* true)

;-----------------------------------------------------------------------------

(defn assoc-multi [m [k v]]
  (assoc m k (if-some [[_ oldv] (find m k)]
               (conj oldv v)
               v)))

(defn set-precision [^long precision ^BigDecimal value]
  (.setScale value precision RoundingMode/HALF_UP))

(defn shift-decimal [dp n]
  (set-precision dp (/ (bigdec n) (bigdec (math/pow 10M dp)))))

(defn count-eols [raw]
  (count (filter #(= % :EOL) (flatten raw))))

(defn remove-eols [raw]
  (filterv #(not= % [:EOL]) raw))

;-----------------------------------------------------------------------------

(insta/defparser grammar "
    file  = <'01'> C sender-id C receiver-id C date C time C file-idx
                   C physical-rec-len C block-size C version <'/'> EOL
            group*
            <'99'> C control-total C group-count C record-count <'/'> <EOL>*

    group = <'02'> C ultimate-receiver-id C originator-id C group-status
                   C date C time C currency-code C date-modifier <'/'> EOL
            account*
            <'98'> C control-total C account-count C record-count <'/'> EOL

    account = <'03'> C account-num C currency-code C account-summary (C account-summary)* <'/'> EOL
              transaction*
              <'49'> C control-total C record-count <'/'> EOL

    account-summary = type-code C amount C item-count C funds-type

    transaction = <'16'> C type-code C amount C funds-type C bank-ref C customer-ref C text EOL

    funds-type = ('' | 'Z' | '0' | '1' | '2' |
                  'V' C date C time |
                  'S' C amount-immed C amount-one-day C amount-two-or-more-day |
                  'D' C <'1'> distrib |
                  'D' C <'2'> distrib distrib |
                  'D' C <'3'> distrib distrib distrib |
                  'D' C <'4'> distrib distrib distrib distrib |
                  'D' C <'5'> distrib distrib distrib distrib distrib)

    distrib = C days C amount

    version                = INT
    physical-rec-len       = INT
    block-size             = INT
    file-idx               = INT
    group-status           = INT
    group-count            = INT
    account-count          = INT
    record-count           = INT
    control-total          = MONEY

    sender-id              = ALPHA
    receiver-id            = ALPHA
    originator-id          = ALPHA
    ultimate-receiver-id   = ALPHA
    bank-ref               = ALPHA
    customer-ref           = ALPHA
    account-num            = ALPHA

    type-code              = ALPHA
    currency-code          = ALPHA
    date-modifier          = INT
    item-count             = INT
    days                   = INT
    amount-immed           = MONEY
    amount-one-day         = MONEY
    amount-two-or-more-day = MONEY
    amount                 = MONEY
    date                   = DATE
    time                   = TIME
    text                   = TEXT

    EOL     = <#'[ \\t]*\\r?\\n'>
    <C>     = <(',' | '/')> EOL <'88,'> | <','>
    TEXT    = #'.*' (EOL <'88,'> #'.*')*
    <ALPHA> = #'[^,/]*'
    MONEY   = #'([+-]?\\d*\\.?\\d+)?'
    INT     = #'([+-]?\\d+)?'
    DATE    = ALPHA
    TIME    = ALPHA")

;; Notes:
;;  EOL - removes whitespace padding between trailing / and end-of-line
;;  C   - spec says (non-text field) continuations should replace trailing , with /
;;        but we allow , for compatibility with files from BMO bank

;-----------------------------------------------------------------------------

(def yyMMdd (DateTimeFormatter/ofPattern "yyMMdd"))
(def HHmm (DateTimeFormatter/ofPattern "HHmm"))

(defn currency-dp [curr-code]
  (condp contains? curr-code
    #{"BRL" "EUR" "JPY" "KMF"
      "XAF" "XOF" "XPF"}      0
    #{"MRO"}                  1
    #{"BHD" "EGP" "IQD" "JOD"
      "KWD" "LYD" "MTL" "OMR"
      "SDP" "TND" "YDD"}      3
    2))

(defn count-records [x]
  (match [x]
    [[:file & more]]    (into [:file [:record-count-actual (inc (count-eols more))]] more)
    [[:group & more]]   (into [:group [:record-count-actual (count-eols more)]] more)
    [[:account & more]] (into [:account [:record-count-actual (count-eols more)]] more)
    :else               x))

(defn parse-ast [x]
  (match [(if (vector? x) (remove-eols x) x)]
    [[:TEXT & more]]            more
    [[:DATE ""]]                nil
    [[:DATE d]]                 (LocalDate/parse d yyMMdd)
    [[:TIME ""]]                nil
    [[:TIME "2400"]]            (LocalTime/of 23 59 59)
    [[:TIME "9999"]]            (LocalTime/of 23 59 59)
    [[:TIME t]]                 (LocalTime/parse t HHmm)
    [[:INT ""]]                 nil
    [[:INT n]]                  (bigint n)
    ;; :MONEY handled in final pass

    [[:funds-type]]             [:funds-type {:type :unknown}]
    [[:funds-type "Z"]]         [:funds-type {:type :unknown}]
    [[:funds-type "0"]]         [:funds-type {:type :avail-immed}]
    [[:funds-type "1"]]         [:funds-type {:type :avail-one-day}]
    [[:funds-type "2"]]         [:funds-type {:type :avail-two-or-more-day}]
    [[:funds-type "V" & more]]  [:funds-type (into {:type :value-dated} more)]
    [[:funds-type "S" & more]]  [:funds-type (into {:type :avail-split} more)]
    [[:funds-type "D" & more]]  [:funds-type (reduce assoc-multi {:type :avail-distrib :distrib []} more)]

    [[:file & more]]            (reduce assoc-multi {:group []} more)
    [[:group & more]]           [:group (reduce assoc-multi {:account []} more)]
    [[:account & more]]         [:account (reduce assoc-multi {:account-summary [] :transaction []} more)]
    [[(k1 :guard keyword?)
      [(k2 :guard keyword?) v2] & more]]  [k1 (into {k2 v2} more)]

    ;; else <key> or <value> or [<key> <value>] or [:EOL]
    :else x))

(defn parse-money [curr-code x]
  (match [x]
    [{:currency-code ""}]                    x
    [{:currency-code cc :account accts}]     (assoc x :account (walk/prewalk #(parse-money cc %) accts))
    [{:currency-code cc :transaction trans}] (assoc x :transaction (walk/prewalk #(parse-money cc %) trans))
    [{:MONEY ""}]                            nil
    [{:MONEY n}]                             (shift-decimal (currency-dp curr-code) n)
    :else                                    x))

;;----------------------------------------------------------------------------
;; Public API

(defn parse
  [bai-text]
  ;; defaulting to "USD" means use 2 decimal places if not specified in file
  (->> (insta/parse grammar bai-text)
       (walk/prewalk count-records)
       (walk/postwalk parse-ast)
       (walk/prewalk #(parse-money "USD" %))))
