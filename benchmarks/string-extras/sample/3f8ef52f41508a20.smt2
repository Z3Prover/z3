; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_81.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ^([a-zA-Z0-9]{1,15})$
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "x"
(define-fun Witness1 () String (str.++ "x" ""))
;witness2: "6949"
(define-fun Witness2 () String (str.++ "6" (str.++ "9" (str.++ "4" (str.++ "9" "")))))

(assert (= regexA (re.++ (str.to_re "")(re.++ ((_ re.loop 1 15) (re.union (re.range "0" "9")(re.union (re.range "A" "Z") (re.range "a" "z")))) (str.to_re "")))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
