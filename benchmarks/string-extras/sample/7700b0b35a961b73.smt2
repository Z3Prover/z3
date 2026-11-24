; origin: https://github.com/vlab-cs-ucsb/ABC/tree/master/test : fixtures/solver/SyntacticOptimizer/test_in_op_01.smt2
(set-logic QF_S)

(declare-fun var_abc () String)

(assert (not (str.in_re var_abc (re.++ (str.to_re "G") (str.to_re "o") (str.to_re "o") (str.to_re "g") (str.to_re "l") (str.to_re "e") (str.to_re "A") (str.to_re "d") (str.to_re "S") (str.to_re "e") (str.to_re "r") (str.to_re "v") (str.to_re "i") (str.to_re "n") (str.to_re "g") (str.to_re "T") (str.to_re "e") (str.to_re "s") (str.to_re "t") (str.to_re "="))))) 

(check-sat)

