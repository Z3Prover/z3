(declare-fun a () String)
(assert (str.in.re a (re.inter (re.* (str.to.re "")) (str.to.re ""))))
(check-sat)
