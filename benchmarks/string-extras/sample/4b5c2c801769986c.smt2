; origin: handwritten/generated (C. Eisenhofer) : hard_len_nonprim_6_cegar_interleaved.smt2
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun k () Int)

;; R = (abc)*
(define-fun R () (RegEx String) (re.* (str.to_re "abc")))

;; NON-PRIMITIVE Constraints interleaved symmetrically
(assert (str.in_re (str.++ x y z) R))
(assert (str.in_re (str.++ z y x) R))

;; We bind the variables to specific linear offsets
(assert (= (str.len x) (+ (str.len z) 2)))
(assert (= (str.len y) (+ (str.len z) 1)))

;; We force the base length of z to be offset from modulo 3
(assert (= (str.len z) (+ (* 3 k) 1)))
(assert (>= k 0))

;; Why it is spectacularly hard:
;; 1. The total length of `x y z` is |x| + |y| + |z| = (|z| + 2) + (|z| + 1) + |z| = 3|z| + 3 = 3(|z| + 1).
;;    Since this is a multiple of 3, the CEGAR abstraction evaluates the total integer length boundaries as completely SAT.
;; 2. Same for `z y x`.
;; 3. Now let's calculate the "Phase Shifts" (Start Indices Modulo 3).
;;    - In `x y z \in (abc)*`, the phase of `z` is precisely the sum of the preceding lengths.
;;      Phase(z) = |x| + |y| = 2|z| + 3. Modulo 3, this is `2|z|`.
;;    - In `z y x \in (abc)*`, the phase of `z` is exactly 0 (it is at the start of the string).
;;    - Since both instances of `z` must match structurally, their internal cyclic sub-automaton states must be compatible.
;;    - However, we constrained $|z| = 3k + 1$.
;;    - Therefore, Phase(z) in the first string is `2(3k + 1) = 6k + 2 \equiv 2 \pmod 3$.
;;    - The phase in the second string is `0 \pmod 3`.
;;    - The cyclic extraction logic proves that the Brzozowski derivative of `z` starts at state `(abc)*` in one formula, 
;;      but uniquely starts at `(cab)*` (shifted by 2) in the other!
;;    - An exact structural match across non-primitive variables in disparate topological roots is fundamentally UNSAT.
(check-sat)