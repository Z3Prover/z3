; origin: handwritten/generated (C. Eisenhofer) : hard_length_1_semilinear_complement.smt2
(set-logic ALL)
(declare-fun x () String)

;; R = (aa)* | (aaa)*
;; Generates lengths {2y} UNION {3z}
;; In integer space, this allows all lengths >= 2 EXCEPT 5, 7, 11... wait, no.
;; Every integer >= 2 EXCEPT those that cannot be purely a multiple of 2 or purely a multiple of 3.
;; E.g., 5 is not 2y or 3z. 7 is not 2y or 3z. 11, 13, 17 are not 2y or 3z!
(define-fun a2 () (RegEx String) (str.to_re "aa"))
(define-fun a3 () (RegEx String) (str.to_re "aaa"))
(define-fun R () (RegEx String) (re.union (re.* a2) (re.* a3)))

;; Constraint: x \in R
(assert (str.in_re x R))

;; Length constraint
(assert (= (str.len x) 17))

;; Why it is hard:
;; Testing the exact CEGAR logic from Section 5.2.
;; The integer solver has no native knowledge of `re.union((aa)*, (aaa)*)` so it blindly accepts |x|=17.
;; A native unwinder would unroll 17 times to discover a dead-end.
;; With the CEGAR length abstraction loop, the generator takes candidate length (17) 
;; and tests intersection \Sigma^17 \sqcap R. 
;; Seeing it is empty, it feeds back the semi-linear bounds, proving that 
;; (17 mod 2 != 0) AND (17 mod 3 != 0), thus closing the arithmetic branch instantly.
(check-sat)