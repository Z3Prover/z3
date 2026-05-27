; Source: Z3Prover/z3test - regressions/smt2/3775.smt2
; Minimal example: distinct applied to a lambda (constant array)

(assert (distinct (lambda ((a Int)) 0)))
(check-sat-using horn)
