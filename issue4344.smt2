(declare-fun a () String)
(assert (str.in.re a (re.inter (str.to.re a) re.allchar)))
(check-sat)