(set-logic LIA)
(declare-const v1 Bool)
(declare-const v2 Bool)
(declare-const i1 Int)
(push 1)
(assert (forall ((q14 Bool)) (not (and q14 q14 (= (mod 26 (abs 26)) (div i1 26)) v1 v2 q14 q14))))
(check-sat-using (then qe-light qflia))
