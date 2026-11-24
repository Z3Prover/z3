; origin: handwritten/generated (C. Eisenhofer) : hard_len_nonprim_3_cegar_diophantine.smt2
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)

;; R = (a^5 b^7)*
(define-fun a5 () (RegEx String) (str.to_re "aaaaa"))
(define-fun b7 () (RegEx String) (str.to_re "bbbbbbb"))
(define-fun R () (RegEx String) (re.* (re.++ a5 b7)))

;; NON-PRIMITIVE Constraint: "a" x "b" y x \in R
(assert (str.in_re (str.++ "a" x "b" y x) R))

;; LENGTH Constraint: |x| = |y|
(assert (= (str.len x) (str.len y)))

;; Why it is spectacularly hard:
;; 1. The string solver binds to `a x b y x \in (a^5 b^7)*`. 
;; 2. Total length of string in R is `1 + |x| + 1 + |y| + |x|`. 
;; 3. Substituting `|x| = |y|`, the length is `3|x| + 2`.
;; 4. R generates lengths mathematically equivalent to `12k`.
;; 5. Equating lengths: `3|x| + 2 = 12k`.
;; 6. Arithmetically: `3|x| = 12k - 2`.
;; 7. Divided by 3: `12k - 2` is NEVER divisible by 3. Diophantine UNSAT.
;; The execution path here demands that CEGAR dynamically intercepts the abstract progression 
;; of two non-primitively intertwined variables (`x` and `y`), extracts their shared gradient, 
;; creates the multi-variable polynomial `3|x| + 2`, intercepts the `12` modulo from the SCC stabilizer extraction, 
;; and logically clashes them in the linear arithmetic constraints natively!
(check-sat)