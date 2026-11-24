; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_357.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = (((0[123456789]|10|11|12)(([1][9][0-9][0-9])|([2][0-9][0-9][0-9]))))
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "W5101993\u00BE"
(define-fun Witness1 () String (str.++ "W" (str.++ "5" (str.++ "1" (str.++ "0" (str.++ "1" (str.++ "9" (str.++ "9" (str.++ "3" (str.++ "\u{be}" ""))))))))))
;witness2: "101999z\x9"
(define-fun Witness2 () String (str.++ "1" (str.++ "0" (str.++ "1" (str.++ "9" (str.++ "9" (str.++ "9" (str.++ "z" (str.++ "\u{09}" "")))))))))

(assert (= regexA (re.++ (re.union (re.++ (re.range "0" "0") (re.range "1" "9"))(re.union (str.to_re (str.++ "1" (str.++ "0" "")))(re.union (str.to_re (str.++ "1" (str.++ "1" ""))) (str.to_re (str.++ "1" (str.++ "2" "")))))) (re.union (re.++ (str.to_re (str.++ "1" (str.++ "9" "")))(re.++ (re.range "0" "9") (re.range "0" "9"))) (re.++ (re.range "2" "2")(re.++ (re.range "0" "9")(re.++ (re.range "0" "9") (re.range "0" "9"))))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
