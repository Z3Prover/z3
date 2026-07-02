; D9  classic commutation equation, UNSAT  (difficulty: hard; 2 vars; calibration point)
; Not from the corpus: a canonical word-equation hardness reference (two-sided equation).
; Word equation:  x . y = y . x  ,  x in a+ , y in b+
; Expected: UNSAT.  xy=yx holds iff x,y are powers of a common word; x is all-a, y is all-b,
; both nonempty -> no common word -> unsatisfiable.

(set-logic QF_S)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-info :category "crafted")
(set-info :source |Synthetic word-equation difficulty ladder, grounded in the data/backrefs.json regex corpus (resharp-node). Encoding: a backreference becomes a REPEATED string variable; a lookaround becomes a membership constraint (positive = & = conjoined str.in_re; negative-over-backref = ~ = not str.contains). Statuses verified by brute force + parity/length arguments.|)
(declare-fun x () String)
(declare-fun y () String)

(assert (str.in_re x (re.+ (str.to_re "a"))))
(assert (str.in_re y (re.+ (str.to_re "b"))))
(assert (= (str.++ x y) (str.++ y x)))

(check-sat)
