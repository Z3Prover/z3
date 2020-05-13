; Copyright (c) 2016 Microsoft Corporation
; GitHub issue
(declare-const src String)

(define-fun digit           () (RegEx String) (re.range "5"  "9"))
(define-fun decimal_strings () (RegEx String) (re.* digit       ))

(assert (= (str.len src) 4))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; [0] src in {5,6,7,8,9}*                        ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(assert (str.in.re src decimal_strings))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; [1] src == "5778" ... without this "hint" z3 says query is unsat ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;(assert (= src "5778"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; [2] str.to.int ( src ) == 5778                     ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(assert (= 5778 (str.to.int src)))

(check-sat)
(get-value (src))