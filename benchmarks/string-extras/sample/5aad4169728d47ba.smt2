; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_906.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ^(\d{4})[.](0{0,1}[1-9]|1[012])[.](0{0,1}[1-9]|[12][0-9]|3[01])[.](\d{2})$
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "6899.12.5.01"
(define-fun Witness1 () String (str.++ "6" (str.++ "8" (str.++ "9" (str.++ "9" (str.++ "." (str.++ "1" (str.++ "2" (str.++ "." (str.++ "5" (str.++ "." (str.++ "0" (str.++ "1" "")))))))))))))
;witness2: "9959.08.29.06"
(define-fun Witness2 () String (str.++ "9" (str.++ "9" (str.++ "5" (str.++ "9" (str.++ "." (str.++ "0" (str.++ "8" (str.++ "." (str.++ "2" (str.++ "9" (str.++ "." (str.++ "0" (str.++ "6" ""))))))))))))))

(assert (= regexA (re.++ (str.to_re "")(re.++ ((_ re.loop 4 4) (re.range "0" "9"))(re.++ (re.range "." ".")(re.++ (re.union (re.++ (re.opt (re.range "0" "0")) (re.range "1" "9")) (re.++ (re.range "1" "1") (re.range "0" "2")))(re.++ (re.range "." ".")(re.++ (re.union (re.++ (re.opt (re.range "0" "0")) (re.range "1" "9"))(re.union (re.++ (re.range "1" "2") (re.range "0" "9")) (re.++ (re.range "3" "3") (re.range "0" "1"))))(re.++ (re.range "." ".")(re.++ ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "")))))))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
