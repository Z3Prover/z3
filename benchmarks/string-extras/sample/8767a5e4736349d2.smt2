; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_1129.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ^([A-Z\d]{3})[A-Z]{2}\d{2}([A-Z\d]{1})([X\d]{1})([A-Z\d]{3})\d{5}$
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "D78MN74WX92249480"
(define-fun Witness1 () String (str.++ "D" (str.++ "7" (str.++ "8" (str.++ "M" (str.++ "N" (str.++ "7" (str.++ "4" (str.++ "W" (str.++ "X" (str.++ "9" (str.++ "2" (str.++ "2" (str.++ "4" (str.++ "9" (str.++ "4" (str.++ "8" (str.++ "0" ""))))))))))))))))))
;witness2: "018IV393X4CE59853"
(define-fun Witness2 () String (str.++ "0" (str.++ "1" (str.++ "8" (str.++ "I" (str.++ "V" (str.++ "3" (str.++ "9" (str.++ "3" (str.++ "X" (str.++ "4" (str.++ "C" (str.++ "E" (str.++ "5" (str.++ "9" (str.++ "8" (str.++ "5" (str.++ "3" ""))))))))))))))))))

(assert (= regexA (re.++ (str.to_re "")(re.++ ((_ re.loop 3 3) (re.union (re.range "0" "9") (re.range "A" "Z")))(re.++ ((_ re.loop 2 2) (re.range "A" "Z"))(re.++ ((_ re.loop 2 2) (re.range "0" "9"))(re.++ (re.union (re.range "0" "9") (re.range "A" "Z"))(re.++ (re.union (re.range "0" "9") (re.range "X" "X"))(re.++ ((_ re.loop 3 3) (re.union (re.range "0" "9") (re.range "A" "Z")))(re.++ ((_ re.loop 5 5) (re.range "0" "9")) (str.to_re "")))))))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
