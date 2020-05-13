(set-logic QF_S)
(declare-fun E () String)
(assert (= (str.++  E "aa" E "ab" E)  (str.++  "a" E E "aabaa") ))
(check-sat)
