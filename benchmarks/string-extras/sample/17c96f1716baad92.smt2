; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_670.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ([0-9a-z_-]+[\.][0-9a-z_-]{1,3})$
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "9._-"
(define-fun Witness1 () String (str.++ "9" (str.++ "." (str.++ "_" (str.++ "-" "")))))
;witness2: "6\u00E8m_.8"
(define-fun Witness2 () String (str.++ "6" (str.++ "\u{e8}" (str.++ "m" (str.++ "_" (str.++ "." (str.++ "8" "")))))))

(assert (= regexA (re.++ (re.++ (re.+ (re.union (re.range "-" "-")(re.union (re.range "0" "9")(re.union (re.range "_" "_") (re.range "a" "z")))))(re.++ (re.range "." ".") ((_ re.loop 1 3) (re.union (re.range "-" "-")(re.union (re.range "0" "9")(re.union (re.range "_" "_") (re.range "a" "z"))))))) (str.to_re ""))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
