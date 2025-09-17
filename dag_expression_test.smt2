; Test case that creates DAG structure with shared subexpressions
; This demonstrates the tree vs DAG traversal issue in SMT checker

(set-logic QF_UF)
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun r (Int) Bool)

; Create shared subexpressions that form a DAG
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

; expr1 = (p x) ∧ (q y)
; expr2 = (q y) ∧ (r z)
; expr3 = (p x) ∧ (r z)

; Combined formula that reuses subexpressions multiple times:
; ((p x) ∧ (q y)) ∧ ((q y) ∧ (r z)) ∧ ((p x) ∧ (r z))
; This creates significant sharing of (p x), (q y), and (r z)

(assert (and (and (p x) (q y))
             (and (q y) (r z))
             (and (p x) (r z))))

(check-sat)