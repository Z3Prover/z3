; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_475.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ^((\.\./|[a-zA-Z0-9_/\-\\])*\.[a-zA-Z0-9]+)$
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "../.78Z"
(define-fun Witness1 () String (str.++ "." (str.++ "." (str.++ "/" (str.++ "." (str.++ "7" (str.++ "8" (str.++ "Z" ""))))))))
;witness2: "../.W"
(define-fun Witness2 () String (str.++ "." (str.++ "." (str.++ "/" (str.++ "." (str.++ "W" ""))))))

(assert (= regexA (re.++ (str.to_re "")(re.++ (re.++ (re.* (re.union (str.to_re (str.++ "." (str.++ "." (str.++ "/" "")))) (re.union (re.range "-" "-")(re.union (re.range "/" "9")(re.union (re.range "A" "Z")(re.union (re.range "\u{5c}" "\u{5c}")(re.union (re.range "_" "_") (re.range "a" "z"))))))))(re.++ (re.range "." ".") (re.+ (re.union (re.range "0" "9")(re.union (re.range "A" "Z") (re.range "a" "z")))))) (str.to_re "")))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
