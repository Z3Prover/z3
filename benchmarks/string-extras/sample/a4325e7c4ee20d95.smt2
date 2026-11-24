; origin: https://github.com/vlab-cs-ucsb/ABC/tree/master/test : bugs/missing_let_support_1.smt
(set-logic ALL)
(declare-const symb_concat String)
(assert (let ((.def_0 (str.++  "conc" symb_concat))) (let ((.def_1 (= .def_0 "concrete"))) .def_1)))
(check-sat)

