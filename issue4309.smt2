(declare-fun a () String)
(assert (str.in.re a (re.loop (str.to.re "") (- 1))))
(assert (< (str.len a) 0))
(check-sat-using ctx-solver-simplify)