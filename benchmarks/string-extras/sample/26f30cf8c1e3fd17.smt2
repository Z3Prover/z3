; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_614.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = [1-8][0-9]{2}[0-9]{5}
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "80984383"
(define-fun Witness1 () String (str.++ "8" (str.++ "0" (str.++ "9" (str.++ "8" (str.++ "4" (str.++ "3" (str.++ "8" (str.++ "3" "")))))))))
;witness2: "\u00F518081499\u00CA\u00BC"
(define-fun Witness2 () String (str.++ "\u{f5}" (str.++ "1" (str.++ "8" (str.++ "0" (str.++ "8" (str.++ "1" (str.++ "4" (str.++ "9" (str.++ "9" (str.++ "\u{ca}" (str.++ "\u{bc}" ""))))))))))))

(assert (= regexA (re.++ (re.range "1" "8")(re.++ ((_ re.loop 2 2) (re.range "0" "9")) ((_ re.loop 5 5) (re.range "0" "9"))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
