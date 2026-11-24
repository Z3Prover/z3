; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/nth-concat-unit-sym-prefix2.smt2
; EXPECT: unsat
; Rewrite::SEQ_NTH_EVAL_SYM must have a complete proof, via RARE rule seq-nth-concat-unit-gen.
(set-logic ALL)
(declare-const p (Seq String))
(declare-const q (Seq String))
(declare-const r (Seq String))
(declare-const x String)
(assert (distinct (seq.nth (seq.++ p q (seq.unit x) r) (+ (seq.len p) (seq.len q))) x))
(check-sat)
