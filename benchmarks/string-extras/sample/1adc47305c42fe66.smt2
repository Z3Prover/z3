; origin: handwritten/generated (C. Eisenhofer) : test_trace.smt2
(declare-const C String)
(declare-const F String)
(assert (= (str.++ "ba" F C "bbaaaabababaa" C "a" C "bb" C) (str.++ C "aaabab" C "bb" C "abbabbabbababb" C "abaaaabaaaab" C "bbbbabbbabaaabb" C "b" C "aabababaabaaabaabbbaa")))
(check-sat)
