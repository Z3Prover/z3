; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_1449.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ^([A-Za-z0-9]\s?)+([,]\s?([A-Za-z0-9]\s?)+)*$
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "2\u00A0s,2J"
(define-fun Witness1 () String (str.++ "2" (str.++ "\u{a0}" (str.++ "s" (str.++ "," (str.++ "2" (str.++ "J" "")))))))
;witness2: "4d\u00A08 ,\u00A0K "
(define-fun Witness2 () String (str.++ "4" (str.++ "d" (str.++ "\u{a0}" (str.++ "8" (str.++ " " (str.++ "," (str.++ "\u{a0}" (str.++ "K" (str.++ " " ""))))))))))

(assert (= regexA (re.++ (str.to_re "")(re.++ (re.+ (re.++ (re.union (re.range "0" "9")(re.union (re.range "A" "Z") (re.range "a" "z"))) (re.opt (re.union (re.range "\u{09}" "\u{0d}")(re.union (re.range " " " ")(re.union (re.range "\u{85}" "\u{85}") (re.range "\u{a0}" "\u{a0}")))))))(re.++ (re.* (re.++ (re.range "," ",")(re.++ (re.opt (re.union (re.range "\u{09}" "\u{0d}")(re.union (re.range " " " ")(re.union (re.range "\u{85}" "\u{85}") (re.range "\u{a0}" "\u{a0}"))))) (re.+ (re.++ (re.union (re.range "0" "9")(re.union (re.range "A" "Z") (re.range "a" "z"))) (re.opt (re.union (re.range "\u{09}" "\u{0d}")(re.union (re.range " " " ")(re.union (re.range "\u{85}" "\u{85}") (re.range "\u{a0}" "\u{a0}")))))))))) (str.to_re ""))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
