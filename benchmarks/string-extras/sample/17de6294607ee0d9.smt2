; origin: https://github.com/cdstanford/regex-smt-benchmarks : det_blowup/unsat/digit10_unsat.smt2
(set-logic QF_S)
;---
; .NET regular expressions restricted to 7-bit characters
; membership in intersection of
; .*\d.{10}
; .*[^\d].{10}
;---
(declare-const x String)
(assert (str.in_re x (re.inter (re.++ (re.++ re.all (re.range "0" "9")) ((_ re.^ 10) re.allchar)) (re.++ (re.++ re.all (re.union (re.range (_ char #x0) "/") (re.range ":" (_ char #x7F)))) ((_ re.^ 10) re.allchar)))))
(check-sat)
;(get-model)
