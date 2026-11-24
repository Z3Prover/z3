; origin: handwritten/generated (C. Eisenhofer) : hard_len_nonprim_1_alternating_parity.smt2
(set-logic ALL)
(declare-fun x () String)
(declare-fun k () Int)

;; R = strings without "aa" and without "bb" (Strictly alternating strings)
(define-fun sig-star () (RegEx String) (re.* re.allchar))
(define-fun aa () (RegEx String) (str.to_re "aa"))
(define-fun bb () (RegEx String) (str.to_re "bb"))
(define-fun no_aa () (RegEx String) (re.comp (re.++ sig-star aa sig-star)))
(define-fun no_bb () (RegEx String) (re.comp (re.++ sig-star bb sig-star)))
(define-fun R () (RegEx String) (re.inter no_aa no_bb))

;; NON-PRIMITIVE Constraint: x "a" x \in R
(assert (str.in_re (str.++ x "a" x) R))

;; LENGTH Constraint: |x| is EVEN
(assert (= (str.len x) (* 2 k)))
(assert (>= k 0))

;; Why it is spectacularly hard:
;; 1. The regex is defined via intersection of complements (extended regex).
;; 2. The membership constraint is non-primitive (x "a" x).
;; 3. The length constraint ties into the parity of the non-primitive topology.
;; Explanation:
;; For `x "a" x` to avoid "aa" or "bb", the string must strictly alternate.
;; Since |x| is even, if `x` alternates, its first and last characters MUST be different 
;; (e.g. "ab", "baba").
;; By consequence, if `x` ends in "b", it MUST start with "a".
;; Let's evaluate `x "a" x`:
;; If `x` ends in "b", then `x` starts with "a".
;; So `x "a" x` = `(..b) a (a...)`.
;; This creates the substring "aa" across the second boundary! UNSAT.
;; If `x` ends in "a", then `...a` + `a` creates "aa" on the first boundary. UNSAT.
;; The SAT solver must unroll `x`, extract the SCC (which naturally tracks even/odd length 
;; cycles via the alternating states), apply the CEGAR length abstraction on those states, 
;; and logically crash into the parity mismatch across the non-primitive boundaries!
(check-sat)