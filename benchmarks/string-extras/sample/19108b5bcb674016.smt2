; origin: handwritten/generated (C. Eisenhofer) : hard_cyclic_8_overapprox_conflict.smt2
(set-logic ALL)
(declare-fun x () String)

;; R = (a|b|c)* a (a|b|c)* b (a|b|c)* c (a|b|c)*
;; Matches any string containing the subsequence "a", "b", "c" in that order.
(define-fun sig-star () (RegEx String) (re.* (re.union (str.to_re "a") (re.union (str.to_re "b") (str.to_re "c")))))
(define-fun a () (RegEx String) (str.to_re "a"))
(define-fun b () (RegEx String) (str.to_re "b"))
(define-fun c () (RegEx String) (str.to_re "c"))
(define-fun R () (RegEx String) (re.++ sig-star (re.++ a (re.++ sig-star (re.++ b (re.++ sig-star (re.++ c sig-star)))))))

;; x is restricted to only 'a' and 'b's.
(define-fun ab-star () (RegEx String) (re.* (re.union a b)))
(assert (str.in_re x ab-star))

;; Constraint: x x x \in R
;; A perfect test for Section 4.2.1: Conflict detection.
;; If the solver naively unwinds x, it will explore an exponentially growing tree of 'a' and 'b' assignments,
;; trying to find 'c' which doesn't exist.
;; However, using the overapproximation mechanism:
;; \Omega(x x x) = ab-star ++ ab-star ++ ab-star = ab-star.
;; And ab-star \sqcap R = \emptyset.
;; The SAT solver should detect this contradiction immediately without any unwinding!
(assert (str.in_re (str.++ x x x) R))
(check-sat)