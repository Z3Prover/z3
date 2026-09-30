; Regression for Z3Prover/z3#10922: sat.smt=true with solver.proof.log used to
; segfault on array axiom propagations. Expected matrix class for smt-clause-log:
; unverified-fallback (the log replays; its `array` hints fall back to the SMT
; checker because there is no array plugin yet). A crash here is a regression.
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const k Int)
(declare-const v Int)
(assert (or (= i j) (= i k)))
(assert (not (= (select (store a i v) j) v)))
(assert (not (= (select (store a i v) k) v)))
(check-sat)
