; D1  square with structural domain  (difficulty: low; 1 var, occ 2, coupling global-structural &)
; Derived from: duplicate-substring lookahead  (.{3,})(?=.*\1)
; Word equation:  x . x  in  (ab)*  ,  x in (a|b)+
; Expected: sat  (x = "ab" -> abab ; note x="a" fails, so the (ab)* constraint bites)

(set-logic QF_S)
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(set-info :category "crafted")
(set-info :source |Synthetic word-equation difficulty ladder, grounded in the data/backrefs.json regex corpus (resharp-node). Encoding: a backreference becomes a REPEATED string variable; a lookaround becomes a membership constraint (positive = & = conjoined str.in_re; negative-over-backref = ~ = not str.contains). Statuses verified by brute force + parity/length arguments.|)
(declare-fun x () String)

(assert (str.in_re x (re.+ (re.union (str.to_re "a") (str.to_re "b")))))
(assert (str.in_re (str.++ x x) (re.* (str.to_re "ab"))))

(check-sat)
