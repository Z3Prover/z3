(declare-fun a () Int)
(assert (distinct a (str.to.int (int.to.str a))))
(check-sat-using fix-dl-var)