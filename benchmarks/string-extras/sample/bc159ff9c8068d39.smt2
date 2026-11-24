; origin: handwritten/generated (C. Eisenhofer) : hard_len_nonprim_4_subsume_len_clash.smt2
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun k () Int)

;; R = ((aa) | (bb))*
(define-fun aa () (RegEx String) (str.to_re "aa"))
(define-fun bb () (RegEx String) (str.to_re "bb"))
(define-fun R () (RegEx String) (re.* (re.union aa bb)))

;; PRIMITIVE Constraint placing x strictly inside the cycle
(assert (str.in_re x R))

;; NON-PRIMITIVE Constraint intertwined with the cycle
(assert (str.in_re (str.++ x y "ab" y) R))

;; LENGTH Constraint: |y| is EVEN
(assert (= (str.len y) (* 2 k)))
(assert (>= k 0))

;; Why it is spectacularly hard:
;; 1. The solver first applies "Cycle SubsumptionStep" (Section 4.2.4): 
;;    Since `x \in R`, `x` is a stabilizer of `R`, so `x` drops perfectly 
;;    off the front of `x y "ab" y \in R`, immediately reducing it to `y "ab" y \in R`.
;; 2. Length-wise, `|y "ab" y|` = `2|y| + 2`, which is ALWAYS even. Length abstraction says SAT.
;; 3. Structurally: `y` must bridge the `ab` block.
;;    To legally form `aa` or `bb` pairs, the "a" in "ab" demands a leading "a" (meaning `y` must end in "a").
;;    The "b" in "ab" demands a trailing "b" (meaning the second `y` must start with "b").
;;    So `y` must start with "b" and end with "a".
;; 4. If `y` is composed of paired blocks from `aa` and `bb`, it can never transition 
;;    from "b" to "a" without straddling a pair! Thus, it must structurally have an ODD length.
;; 5. The integer solver statically asserts `|y|` is EVEN.
;; 6. UNSAT!
;; This benchmark seamlessly merges: Non-primitive sequences, Cycle Subsumption, 
;; structural overlaps resolving to parity fragments, and a CEGAR integer conflict!
(check-sat)