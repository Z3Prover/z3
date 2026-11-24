; origin: handwritten/generated (C. Eisenhofer) : test4.smt2
(declare-const x String)
(declare-const y String)
(assert (= (str.len x) 1))
(assert (str.in_re y (re.* (re.range "a" "z"))))
; regex: one char in [a-c] followed by one or more chars in [d-f]
(assert (str.in_re (str.++ x y)
   (re.++ (re.range "a" "c") (re.+ (re.range "d" "f")))))
(check-sat)

