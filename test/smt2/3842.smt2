(set-logic HORN)
(set-option :rewriter.eq2ineq true)
(set-option :rewriter.flat false)
(set-option :rewriter.arith_lhs true)
(set-option :fp.spacer.native_mbp false)
(set-option :fp.datalog.subsumption false)
;(set-option :fp.xform.magic true)
(set-option :fp.xform.inline_eager false)
(assert (forall ((q17 Real) (q18 Real) (q19 Real) (q20 Real) (q21 Real) (q22 Bool)) false))
(assert (forall ((q23 Real) (q24 Bool)) false))
(assert (forall ((q35 Real) (q36 Real) (q37 Bool)) false))
(assert (forall ((q38 Real) (q39 Real) (q40 Bool)) false))
(assert (forall ((q46 Real) (q47 Bool)) false))
(assert (forall ((q60 Real) (q61 Bool)) false))
(assert (forall ((q62 Real) (q63 Real) (q64 Bool)) (=> (= (+ 0.10788942 q63 q62 q62) 75.0 q63) false)))
(check-sat)