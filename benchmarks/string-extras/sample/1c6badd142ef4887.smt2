; origin: handwritten/generated (C. Eisenhofer) : hard_cyclic_11_deep_unrolling.smt2
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)

;; Pattern 1: x and y must weave symmetrically
;; R1 = (ab|ba)*
(define-fun ab () (RegEx String) (str.to_re "ab"))
(define-fun ba () (RegEx String) (str.to_re "ba"))
(define-fun R1 () (RegEx String) (re.* (re.union ab ba)))

;; Constraint: x "a" y "b" x \in R1
(assert (str.in_re (str.++ x "a" y "b" x) R1))

;; Constraint: x "b" y "a" x \in R1
(assert (str.in_re (str.++ x "b" y "a" x) R1))

;; Deep unrolling stress test: 
;; Two variables intertwined through overlapping Nielsen splits.
;; Exploring whether the left-quotient stabilizers can cooperatively untangle multiple variables
;; acting as overlapping prefixes and infixes on the same cyclic regex graph.
(check-sat)