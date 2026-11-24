; origin: https://github.com/vlab-cs-ucsb/ABC/tree/master/test : bugs/missing_let_support_7.smt
(set-logic ALL)
(declare-const Symb_2_0_4 String)
(assert (let ((.def_0 (<= (str.len Symb_2_0_4) 4))) .def_0))
(assert (let ((.def_0 (< (str.len Symb_2_0_4) 4))) .def_0))
(assert (let ((.def_0 (<= 4 (str.len Symb_2_0_4)))) .def_0))
(assert (let ((.def_0 (< 4 (str.len Symb_2_0_4)))) .def_0))
(check-sat)

