; origin: handwritten/generated (C. Eisenhofer) : hard_len_nonprim_7_difference_parity.smt2
(set-logic ALL)
(declare-fun x () String)

;; R1 = (ab)*
;; R2 = (abab)* = exactly an EVEN number of (ab) repetitions.
;; R = R1 INTERSECT ~(R2)
;; Operationally, R represents strings consisting of EXACTLY an ODD number of "ab" pairs.
;; Concretely: R accepts "ab", "ababab", "ababababab", etc. ONLY lengths 2, 6, 10, ... (4n+2).
(define-fun ab () (RegEx String) (str.to_re "ab"))
(define-fun abab () (RegEx String) (str.to_re "abab"))
(define-fun R1 () (RegEx String) (re.* ab))
(define-fun R2 () (RegEx String) (re.* abab))
(define-fun R () (RegEx String) (re.inter R1 (re.comp R2)))

;; NON-PRIMITIVE Constraint
(assert (str.in_re (str.++ x x) R))
(assert (> (str.len x) 100))

;; Why it is spectacularly hard:
;; 1. The CEGAR length engine tests the structural length of R. It deduces mathematically that the only valid lengths form the progression `4k + 2`.
;; 2. It equates this with the total string length: `|x x| = 2|x|`.
;; 3. Linear arithmetic easily deduces: `2|x| = 4k + 2 \implies |x| = 2k + 1`. The integer solver mathematically demands $|x|$ MUST be ODD.
;; 4. BUT! For `x x` to be an element of `(ab)*` structurally, `x` MUST itself belong to `(ab)*`. 
;;    (If `x` has odd length and alternates, `x x` creates an "aa" or "bb" boundary directly in the middle, failing `R1`!)
;; 5. Since `x` must functionally be in `(ab)*`, its structural length MUST be EVEN!
;; 6. The CEGAR Length derivation forces ODD. The SCC Structural derivation forces EVEN.
;; 
;; This creates the ultimate modular paradox, instantly verifying if the SMT core can natively exchange structural constraints and 
;; numerical progressions back and forth between extended regex complements without falling into deep infinite unwinding trees.
(check-sat)