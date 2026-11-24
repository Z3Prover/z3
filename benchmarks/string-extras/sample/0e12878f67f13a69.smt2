; origin: handwritten/generated (C. Eisenhofer) : hard_cyclic_13_parallel_graphs.smt2
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

;; Test: Parallel Graph Derivation via Global Split
(define-fun ab () (RegEx String) (str.to_re "ab"))
(define-fun ba () (RegEx String) (str.to_re "ba"))
(define-fun R-ab () (RegEx String) (re.* ab))
(define-fun R-ba () (RegEx String) (re.* ba))

;; Constraints enforcing cyclic structures across multiple shifted domains simultaneously:
(assert (str.in_re (str.++ x y) R-ab))
(assert (str.in_re (str.++ y z) R-ba))
(assert (str.in_re (str.++ z x) R-ab))

;; Force them out of the trivial \epsilon solutions using symbolic alphabet prefixes
(define-fun starts_a () (RegEx String) (re.++ (str.to_re "a") (re.* re.allchar)))
(define-fun starts_b () (RegEx String) (re.++ (str.to_re "b") (re.* re.allchar)))
(assert (str.in_re x starts_a))
(assert (str.in_re y starts_b))
(assert (str.in_re z starts_a))

;; Why it is hard:
;; From the primitive start bounds:
;; x starts with 'a'.
;; y starts with 'b'.
;; z starts with 'a'.
;; 
;; If x = (ab)^n a, then y MUST be (ba)^m b (to make xy \in (ab)*).
;; If y = (ba)^m b, then z MUST be (ab)^k a (to make yz \in (ba)*).
;; If z = (ab)^k a, then zx = (ab)^k a (ab)^n a = ... a a ...
;; But "aa" is NOT in (ab)*, so the third intersection structurally fails.
;;
;; Since Nielsen substitution applies globally across ALL constraints, the solver must 
;; advance the Brzozowski derivatives simultaneously in ALL THREE constraint graphs when unwinding. 
;; When x stabilizers are extracted, they must be projected symmetrically across graphs that
;; have different cyclic phases!
(check-sat)