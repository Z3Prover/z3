(declare-fun t () Int)
(assert (> t (bv2nat ((_ int2bv 1) t))))
(check-sat-using (then qfidl smt))