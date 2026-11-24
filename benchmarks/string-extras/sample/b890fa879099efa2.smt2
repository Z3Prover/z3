; origin: handwritten/generated (C. Eisenhofer) : hard_length_2_cegar_gradient.smt2
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () Int)

;; R = (a^12)*
(define-fun a12 () (RegEx String) (str.to_re "aaaaaaaaaaaa"))
(define-fun R () (RegEx String) (re.* a12))

(assert (str.in_re x R))

;; We assert an infinite progression of spurious lengths: |x| = 12y + 7
(assert (>= y 0))
(assert (= (str.len x) (+ (* 12 y) 7)))

;; Why it is hard:
;; Testing the "Spurious Progression Blocking" from Section 5.2.
;; The integer solver will propose |x| = 7, 19, 31, 43, 55, ... 
;; Naively passing these lengths back and forth from the string theory to the arithmetic solver
;; results in an infinite search (since there are infinitely many such numbers).
;; The paper describes extracting the gradient (a=12, b=7). 
;; The intersection \Sigma^7 (\Sigma^12)* \sqcap R is tested structurally, and fails.
;; This allows the solver to issue the generalized blocking clause:
;; x \in L(R) \implies (|x| - 7 < 0 \lor 12 \nmid (|x| - 7))
;; which invalidates the ENTIRE arithmetic progression 12y+7 at once!
(check-sat)