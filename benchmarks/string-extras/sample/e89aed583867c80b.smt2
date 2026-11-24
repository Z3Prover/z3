; origin: handwritten/generated (C. Eisenhofer) : test3.smt2
(declare-const x String) (declare-const y String)
(assert (= (str.len x) 0)) (assert (= (str.len y) 0))
(assert (str.in_re (str.++ x y) (re.comp (re.* (re.range "a" "a")))))
(check-sat)
