
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger from a bug report by wanderseeme (https://github.com/Z3Prover/z3/issues/201).")

(declare-datatypes () 
	(
		(Tuple (tuple 
				   (location Int) 
				   (_b Bool) 
				   (_i15 (_ BitVec 15)) 
				   (_i32 (_ BitVec 32)) 
				   (_i64 (_ BitVec 64)) 
				   (_f (_ FloatingPoint 8 24)) 
				   ))))

(declare-const X Tuple)
(declare-const Y Tuple)

(assert (fp.lt (_f X) (_f Y)))
(assert (fp.gt (_f X) (_f Y)))

(check-sat)
(check-sat-using smt)
(exit)
