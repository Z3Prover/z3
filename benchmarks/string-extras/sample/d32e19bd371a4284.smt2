; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/seq-nth-undef-unsat.smt2
; COMMAND-LINE:
;EXPECT: unsat
(set-logic ALL)
(declare-fun s () (Seq Int))
(declare-fun n () Int)

(assert (=> (and (<= 0 n ) (< n (seq.len s))) (= (seq.nth s n) 6)))
(assert (=> (>= 0 n) (= (seq.nth s n) 7)))
(assert (=> (>= n (seq.len s)) (= (seq.nth s n) 8)))
(assert (distinct (seq.unit 6) (seq.extract s n 1)))
(assert (distinct (seq.unit 7) (seq.extract s n 1)))
(assert (distinct (seq.unit 8) (seq.extract s n 1)))
(assert (> n 0))
(assert (< n (seq.len s)))
(assert (> (seq.len s) 0))
(check-sat)

