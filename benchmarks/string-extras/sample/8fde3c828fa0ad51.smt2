; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_1248.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ^([4]{1})([0-9]{12,15})$
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "428338889989989"
(define-fun Witness1 () String (str.++ "4" (str.++ "2" (str.++ "8" (str.++ "3" (str.++ "3" (str.++ "8" (str.++ "8" (str.++ "8" (str.++ "9" (str.++ "9" (str.++ "8" (str.++ "9" (str.++ "9" (str.++ "8" (str.++ "9" ""))))))))))))))))
;witness2: "496145186980933"
(define-fun Witness2 () String (str.++ "4" (str.++ "9" (str.++ "6" (str.++ "1" (str.++ "4" (str.++ "5" (str.++ "1" (str.++ "8" (str.++ "6" (str.++ "9" (str.++ "8" (str.++ "0" (str.++ "9" (str.++ "3" (str.++ "3" ""))))))))))))))))

(assert (= regexA (re.++ (str.to_re "")(re.++ (re.range "4" "4")(re.++ ((_ re.loop 12 15) (re.range "0" "9")) (str.to_re ""))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
