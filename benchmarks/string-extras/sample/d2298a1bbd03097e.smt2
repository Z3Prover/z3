; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_1726.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ^([0-1]([\s-./\\])?)?(\(?[2-9]\d{2}\)?|[2-9]\d{3})([\s-./\\])?(\d{3}([\s-./\\])?\d{4}|[a-zA-Z0-9]{7})$
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "90181998302"
(define-fun Witness1 () String (str.++ "9" (str.++ "0" (str.++ "1" (str.++ "8" (str.++ "1" (str.++ "9" (str.++ "9" (str.++ "8" (str.++ "3" (str.++ "0" (str.++ "2" ""))))))))))))
;witness2: "888900\u00858568"
(define-fun Witness2 () String (str.++ "8" (str.++ "8" (str.++ "8" (str.++ "9" (str.++ "0" (str.++ "0" (str.++ "\u{85}" (str.++ "8" (str.++ "5" (str.++ "6" (str.++ "8" ""))))))))))))

(assert (= regexA (re.++ (str.to_re "")(re.++ (re.opt (re.++ (re.range "0" "1") (re.opt (re.union (re.range "\u{09}" "\u{0d}")(re.union (re.range " " " ")(re.union (re.range "-" "/")(re.union (re.range "\u{5c}" "\u{5c}")(re.union (re.range "\u{85}" "\u{85}") (re.range "\u{a0}" "\u{a0}")))))))))(re.++ (re.union (re.++ (re.opt (re.range "(" "("))(re.++ (re.range "2" "9")(re.++ ((_ re.loop 2 2) (re.range "0" "9")) (re.opt (re.range ")" ")"))))) (re.++ (re.range "2" "9") ((_ re.loop 3 3) (re.range "0" "9"))))(re.++ (re.opt (re.union (re.range "\u{09}" "\u{0d}")(re.union (re.range " " " ")(re.union (re.range "-" "/")(re.union (re.range "\u{5c}" "\u{5c}")(re.union (re.range "\u{85}" "\u{85}") (re.range "\u{a0}" "\u{a0}")))))))(re.++ (re.union (re.++ ((_ re.loop 3 3) (re.range "0" "9"))(re.++ (re.opt (re.union (re.range "\u{09}" "\u{0d}")(re.union (re.range " " " ")(re.union (re.range "-" "/")(re.union (re.range "\u{5c}" "\u{5c}")(re.union (re.range "\u{85}" "\u{85}") (re.range "\u{a0}" "\u{a0}"))))))) ((_ re.loop 4 4) (re.range "0" "9")))) ((_ re.loop 7 7) (re.union (re.range "0" "9")(re.union (re.range "A" "Z") (re.range "a" "z"))))) (str.to_re ""))))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
