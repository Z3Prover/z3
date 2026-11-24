; origin: handwritten/generated (C. Eisenhofer) : hard_cyclic_3.smt2
(set-logic ALL)
(declare-fun x () String)

;; R = (ab | bca | cab)*
(define-fun ab () (RegEx String) (str.to_re "ab"))
(define-fun bca () (RegEx String) (str.to_re "bca"))
(define-fun cab () (RegEx String) (str.to_re "cab"))
(define-fun R () (RegEx String) (re.* (re.union ab (re.union bca cab))))

;; Constraint: x "a" x \in R
(assert (str.in_re (str.++ x "a" x) R))
(check-sat)
