; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_970.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ^.*(([^\.][\.][wW][mM][aA])|([^\.][\.][mM][pP][3]))$
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "\u00A1.wmA"
(define-fun Witness1 () String (str.++ "\u{a1}" (str.++ "." (str.++ "w" (str.++ "m" (str.++ "A" ""))))))
;witness2: "s\u00D1.WmA"
(define-fun Witness2 () String (str.++ "s" (str.++ "\u{d1}" (str.++ "." (str.++ "W" (str.++ "m" (str.++ "A" "")))))))

(assert (= regexA (re.++ (str.to_re "")(re.++ (re.* (re.union (re.range "\u{00}" "\u{09}") (re.range "\u{0b}" "\u{ff}")))(re.++ (re.union (re.++ (re.union (re.range "\u{00}" "-") (re.range "/" "\u{ff}"))(re.++ (re.range "." ".")(re.++ (re.union (re.range "W" "W") (re.range "w" "w"))(re.++ (re.union (re.range "M" "M") (re.range "m" "m")) (re.union (re.range "A" "A") (re.range "a" "a")))))) (re.++ (re.union (re.range "\u{00}" "-") (re.range "/" "\u{ff}"))(re.++ (re.range "." ".")(re.++ (re.union (re.range "M" "M") (re.range "m" "m"))(re.++ (re.union (re.range "P" "P") (re.range "p" "p")) (re.range "3" "3")))))) (str.to_re ""))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
