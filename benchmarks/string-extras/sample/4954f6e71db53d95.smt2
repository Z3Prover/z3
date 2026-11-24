; origin: https://github.com/vlab-cs-ucsb/ABC/tree/master/test : bugs/missing_let_support_5.smt
(set-logic ALL)
(declare-const symb_length String)
(assert (let ((.def_0 (= (str.len symb_length) 14))) .def_0))
(check-sat)

