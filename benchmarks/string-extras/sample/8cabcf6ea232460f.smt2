; origin: handwritten/generated (C. Eisenhofer) : t2.smt2
(set-logic ALL)
(declare-fun x () String)
(assert (str.in_re (str.++ x "abab" x "baba" x) 
    (re.++ 
        (re.comp (re.++ (re.* re.allchar) (str.to_re "aaaa") (re.* re.allchar)))
        (re.inter (re.* (re.union (str.to_re "ab") (str.to_re "ba"))) (re.comp (re.++ (re.* re.allchar) (str.to_re "bbbb") (re.* re.allchar))))
    )
))
(check-sat)