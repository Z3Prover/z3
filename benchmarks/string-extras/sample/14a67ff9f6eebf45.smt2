; origin: handwritten/generated (C. Eisenhofer) : t1.smt2
(set-logic ALL)
(declare-fun x () String)
(assert (str.in_re (str.++ x "a" x "b" x) 
    (re.++ 
        (re.* (re.comp (re.++ (re.* re.allchar) (str.to_re "aa") (re.* re.allchar))))
        (re.inter (re.* (re.union (str.to_re "a") (str.to_re "b"))) (re.comp (re.++ (re.* re.allchar) (str.to_re "bb") (re.* re.allchar))))
    )
))
(check-sat)