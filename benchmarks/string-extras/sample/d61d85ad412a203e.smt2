; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_1417.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ^[0-9]{5}$
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "49987"
(define-fun Witness1 () String (str.++ "4" (str.++ "9" (str.++ "9" (str.++ "8" (str.++ "7" ""))))))
;witness2: "96905"
(define-fun Witness2 () String (str.++ "9" (str.++ "6" (str.++ "9" (str.++ "0" (str.++ "5" ""))))))

(assert (= regexA (re.++ (str.to_re "")(re.++ ((_ re.loop 5 5) (re.range "0" "9")) (str.to_re "")))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
