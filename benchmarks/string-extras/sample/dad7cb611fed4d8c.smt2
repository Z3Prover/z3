; origin: handwritten/generated (C. Eisenhofer) : hard_cyclic_9_subsumption.smt2
(set-logic ALL)
(declare-fun x () String)

;; R = (aa)* b (aa)*
(define-fun aa () (RegEx String) (str.to_re "aa"))
(define-fun aa-star () (RegEx String) (re.* aa))
(define-fun b () (RegEx String) (str.to_re "b"))
(define-fun R () (RegEx String) (re.++ aa-star (re.++ b aa-star)))

;; Primitive constraint limiting x
(assert (str.in_re x aa-star))

;; Constraint: x "b" x \in R
;; A deliberate test for Section 4.2.4: Cycle Subsumption Step.
;; Since x \in (aa)* and (aa)* is a left stabilizer of R (because taking any word from (aa)* and quotienting R leaves R unchanged),
;; the leading variable `x` physically drops out of `x "b" x \in R` via the Subsumption rule.
;; This leaves `"b" x \in R`. 
;; Taking the derivative with respect to "b" cleanly leaves `x \in (aa)*`.
;; A naive tool will endlessly unroll `x \mapsto a x'` -> `x \mapsto a a x''` searching for the "b".
;; But Subsumption cuts the knot instantly.
(assert (str.in_re (str.++ x "b" x) R))
(check-sat)