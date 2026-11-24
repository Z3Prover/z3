; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_669.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ^[A-ZÄÖÜ]{1,3}\-[ ]{0,1}[A-Z]{0,2}[0-9]{1,4}[H]{0,1}
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "\u00C4-33H"
(define-fun Witness1 () String (str.++ "\u{c4}" (str.++ "-" (str.++ "3" (str.++ "3" (str.++ "H" ""))))))
;witness2: "\u00C4-J99H\u00B3"
(define-fun Witness2 () String (str.++ "\u{c4}" (str.++ "-" (str.++ "J" (str.++ "9" (str.++ "9" (str.++ "H" (str.++ "\u{b3}" ""))))))))

(assert (= regexA (re.++ (str.to_re "")(re.++ ((_ re.loop 1 3) (re.union (re.range "A" "Z")(re.union (re.range "\u{c4}" "\u{c4}")(re.union (re.range "\u{d6}" "\u{d6}") (re.range "\u{dc}" "\u{dc}")))))(re.++ (re.range "-" "-")(re.++ (re.opt (re.range " " " "))(re.++ ((_ re.loop 0 2) (re.range "A" "Z"))(re.++ ((_ re.loop 1 4) (re.range "0" "9")) (re.opt (re.range "H" "H"))))))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
