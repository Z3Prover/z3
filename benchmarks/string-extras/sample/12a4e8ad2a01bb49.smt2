; origin: handwritten/generated (C. Eisenhofer) : hard_len_nonprim_2_cyclic_phase_shift.smt2
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun k () Int)

;; R = (abc)*
(define-fun R () (RegEx String) (re.* (str.to_re "abc")))

;; NON-PRIMITIVE Constraint: x y x \in R
(assert (str.in_re (str.++ x y x) R))

;; We ensure x is not empty
(assert (> (str.len x) 0))

;; LENGTH Constraint: |x| + |y| == 1 mod 3
;; Expressed arithmetically: |x| + |y| = 3k + 1
(assert (= (+ (str.len x) (str.len y)) (+ (* 3 k) 1)))
(assert (>= k 0))

;; Why it is spectacularly hard:
;; 1. The constraint `x y x` uses repeated variables shifted by an unknown infix `y`.
;; 2. Since `x` appears twice in `(abc)*`, both copies must parse perfectly against the cyclic `(abc)` pattern.
;; 3. If `x` begins at index 0 (phase 0 mod 3), and `x` is not empty (it starts with "a"), 
;;    then EVERY occurrence of `x` must start at an index perfectly divisible by 3 (phase 0).
;; 4. The second `x` begins at index `|x| + |y|`.
;; 5. The length constraint statically forces `|x| + |y|` to be 1 mod 3 (phase 1).
;; 6. This implies the second `x` would have to start matching at "b", which contradicts that `x` starts with "a".
;; For the string solver: Structural unwinding is blind to `|x| + |y| = 3k + 1` until it hits the CEGAR length abstraction loop. 
;; The solver has to extract the `(abc)*` projection for the first `x`, bind `y` sequentially, 
;; recognize that `y` spans a topological path length of `|y|`, and realize that mathematically 
;; the offset completely violates the state reachability for the resumption of `x`.
(check-sat)