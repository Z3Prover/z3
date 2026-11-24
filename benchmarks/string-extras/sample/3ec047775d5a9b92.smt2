; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_1847.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = 20\d{2}(-|\/)((0[1-9])|(1[0-2]))(-|\/)((0[1-9])|([1-2][0-9])|(3[0-1]))(T|\s)(([0-1][0-9])|(2[0-3])):([0-5][0-9]):([0-5][0-9])
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "2068-08/28T08:58:31\x9"
(define-fun Witness1 () String (str.++ "2" (str.++ "0" (str.++ "6" (str.++ "8" (str.++ "-" (str.++ "0" (str.++ "8" (str.++ "/" (str.++ "2" (str.++ "8" (str.++ "T" (str.++ "0" (str.++ "8" (str.++ ":" (str.++ "5" (str.++ "8" (str.++ ":" (str.++ "3" (str.++ "1" (str.++ "\u{09}" "")))))))))))))))))))))
;witness2: "2089-11-31\u00A004:48:52"
(define-fun Witness2 () String (str.++ "2" (str.++ "0" (str.++ "8" (str.++ "9" (str.++ "-" (str.++ "1" (str.++ "1" (str.++ "-" (str.++ "3" (str.++ "1" (str.++ "\u{a0}" (str.++ "0" (str.++ "4" (str.++ ":" (str.++ "4" (str.++ "8" (str.++ ":" (str.++ "5" (str.++ "2" ""))))))))))))))))))))

(assert (= regexA (re.++ (str.to_re (str.++ "2" (str.++ "0" "")))(re.++ ((_ re.loop 2 2) (re.range "0" "9"))(re.++ (re.union (re.range "-" "-") (re.range "/" "/"))(re.++ (re.union (re.++ (re.range "0" "0") (re.range "1" "9")) (re.++ (re.range "1" "1") (re.range "0" "2")))(re.++ (re.union (re.range "-" "-") (re.range "/" "/"))(re.++ (re.union (re.++ (re.range "0" "0") (re.range "1" "9"))(re.union (re.++ (re.range "1" "2") (re.range "0" "9")) (re.++ (re.range "3" "3") (re.range "0" "1"))))(re.++ (re.union (re.range "\u{09}" "\u{0d}")(re.union (re.range " " " ")(re.union (re.range "T" "T")(re.union (re.range "\u{85}" "\u{85}") (re.range "\u{a0}" "\u{a0}")))))(re.++ (re.union (re.++ (re.range "0" "1") (re.range "0" "9")) (re.++ (re.range "2" "2") (re.range "0" "3")))(re.++ (re.range ":" ":")(re.++ (re.++ (re.range "0" "5") (re.range "0" "9"))(re.++ (re.range ":" ":") (re.++ (re.range "0" "5") (re.range "0" "9")))))))))))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
