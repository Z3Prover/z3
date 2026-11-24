; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_743.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = [+]?[\x20]*(?<int>\d+)?[-\x20]*[\(]?(?<area>[2-9]\d{2})[\)\-\x20]*(?<pbx>[0-9]{3})[-\x20]*(?<num>[0-9]{4})
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "\u00F46838) 089--1197"
(define-fun Witness1 () String (str.++ "\u{f4}" (str.++ "6" (str.++ "8" (str.++ "3" (str.++ "8" (str.++ ")" (str.++ " " (str.++ "0" (str.++ "8" (str.++ "9" (str.++ "-" (str.++ "-" (str.++ "1" (str.++ "1" (str.++ "9" (str.++ "7" "")))))))))))))))))
;witness2: "\u00BC     415 006 - --2689\u00C7\u00A2"
(define-fun Witness2 () String (str.++ "\u{bc}" (str.++ " " (str.++ " " (str.++ " " (str.++ " " (str.++ " " (str.++ "4" (str.++ "1" (str.++ "5" (str.++ " " (str.++ "0" (str.++ "0" (str.++ "6" (str.++ " " (str.++ "-" (str.++ " " (str.++ "-" (str.++ "-" (str.++ "2" (str.++ "6" (str.++ "8" (str.++ "9" (str.++ "\u{c7}" (str.++ "\u{a2}" "")))))))))))))))))))))))))

(assert (= regexA (re.++ (re.opt (re.range "+" "+"))(re.++ (re.* (re.range " " " "))(re.++ (re.opt (re.+ (re.range "0" "9")))(re.++ (re.* (re.union (re.range " " " ") (re.range "-" "-")))(re.++ (re.opt (re.range "(" "("))(re.++ (re.++ (re.range "2" "9") ((_ re.loop 2 2) (re.range "0" "9")))(re.++ (re.* (re.union (re.range " " " ")(re.union (re.range ")" ")") (re.range "-" "-"))))(re.++ ((_ re.loop 3 3) (re.range "0" "9"))(re.++ (re.* (re.union (re.range " " " ") (re.range "-" "-"))) ((_ re.loop 4 4) (re.range "0" "9")))))))))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
