; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_1111.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ^([A-Z]{2}[0-9]{3})|([A-Z]{2}[\ ][0-9]{3})$
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "ZK682\u00A9@"
(define-fun Witness1 () String (str.++ "Z" (str.++ "K" (str.++ "6" (str.++ "8" (str.++ "2" (str.++ "\u{a9}" (str.++ "@" ""))))))))
;witness2: "_8GE 819"
(define-fun Witness2 () String (str.++ "_" (str.++ "8" (str.++ "G" (str.++ "E" (str.++ " " (str.++ "8" (str.++ "1" (str.++ "9" "")))))))))

(assert (= regexA (re.union (re.++ (str.to_re "") (re.++ ((_ re.loop 2 2) (re.range "A" "Z")) ((_ re.loop 3 3) (re.range "0" "9")))) (re.++ (re.++ ((_ re.loop 2 2) (re.range "A" "Z"))(re.++ (re.range " " " ") ((_ re.loop 3 3) (re.range "0" "9")))) (str.to_re "")))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
