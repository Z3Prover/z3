; Copyright Microsoft 2017
; repro for GitHub Issue 1092

	(declare-datatypes () ((Destination (d1) (d2) (d3) (d4))))
	(declare-datatypes () ((Source (s1) (s2) (s3) (s4))))
	(declare-fun f_allocate (Source) Destination)
	(assert (forall ((x Source)) (exists ((y Destination)) (= (f_allocate x) y))))
	(set-option :opt.priority pareto)
        (declare-const x Int)
        (maximize x)
	(check-sat)
        (get-objectives)
