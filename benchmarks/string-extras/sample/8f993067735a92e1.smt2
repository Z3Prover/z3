; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_1704.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ^\d{3,3}\.\d{0,2}$|^E\d{3,3}\.\d{0,2}$
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "929."
(define-fun Witness1 () String (str.++ "9" (str.++ "2" (str.++ "9" (str.++ "." "")))))
;witness2: "189.94"
(define-fun Witness2 () String (str.++ "1" (str.++ "8" (str.++ "9" (str.++ "." (str.++ "9" (str.++ "4" "")))))))

(assert (= regexA (re.union (re.++ (str.to_re "")(re.++ ((_ re.loop 3 3) (re.range "0" "9"))(re.++ (re.range "." ".")(re.++ ((_ re.loop 0 2) (re.range "0" "9")) (str.to_re ""))))) (re.++ (str.to_re "")(re.++ (re.range "E" "E")(re.++ ((_ re.loop 3 3) (re.range "0" "9"))(re.++ (re.range "." ".")(re.++ ((_ re.loop 0 2) (re.range "0" "9")) (str.to_re "")))))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
