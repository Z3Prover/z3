(declare-fun var810 () String)
(assert (and (forall ((va String)) (or (= "B" var810) (not (str.in_re va (re.union (str.to_re "z") (str.to_re (str.substr "z" 0 (str.len var810)))))))))
(check-sat-using ctx-solver-simplify)
