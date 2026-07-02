; D5  two variables, global structural (SAT variant of user seed)  (difficulty: medium; 2 vars, occ 2 each)
; Derived from: user seed (?:(?=^(ab)*$))(a*)(b*)(a|b)\2\1, middle char removed (even-length cousin)
; Word equation:  x . y . x . y  in  (ab)*  ,  x in a+ , y in b+
; Expected: sat  (x="a", y="b" -> abab ; alternation forces exactly this for nonempty x,y)

(set-logic QF_S)
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(set-info :category "crafted")
(set-info :source |Synthetic word-equation difficulty ladder, grounded in the data/backrefs.json regex corpus (resharp-node). Encoding: a backreference becomes a REPEATED string variable; a lookaround becomes a membership constraint (positive = & = conjoined str.in_re; negative-over-backref = ~ = not str.contains). Statuses verified by brute force + parity/length arguments.|)
(declare-fun x () String)
(declare-fun y () String)

(assert (str.in_re x (re.+ (str.to_re "a"))))
(assert (str.in_re y (re.+ (str.to_re "b"))))
(assert (str.in_re (str.++ x y x y) (re.* (str.to_re "ab"))))

(check-sat)
