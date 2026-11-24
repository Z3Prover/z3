; origin: handwritten/generated (C. Eisenhofer) : test2.smt2
(declare-const x String) (declare-const y String)
(assert (= (str.len x) 1)) (assert (= (str.len y) 1))
(assert (str.in_re (str.++ x y)
   (re.++ (re.union (str.to_re "a") (str.to_re "b")) (str.to_re "c"))))
(check-sat)

