; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_710.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = [\s0-9a-zA-Z\;\"\,\<\>\\?\+\=\)\(\\*\&\%\\$\#\.]*
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: ""
(define-fun Witness1 () String "")
;witness2: "\u00A1\u008AR"
(define-fun Witness2 () String (str.++ "\u{a1}" (str.++ "\u{8a}" (str.++ "R" ""))))

(assert (= regexA (re.* (re.union (re.range "\u{09}" "\u{0d}")(re.union (re.range " " " ")(re.union (re.range "\u{22}" "&")(re.union (re.range "(" ",")(re.union (re.range "." ".")(re.union (re.range "0" "9")(re.union (re.range ";" "?")(re.union (re.range "A" "Z")(re.union (re.range "\u{5c}" "\u{5c}")(re.union (re.range "a" "z")(re.union (re.range "\u{85}" "\u{85}") (re.range "\u{a0}" "\u{a0}")))))))))))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
