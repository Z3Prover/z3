; D4  global structural, parity-TUNABLE  (difficulty: medium; 1 var, occ 2, coupling global-structural &)
; Derived from: D1 generalized with a fixed middle delimiter d of tunable length.
; Word equation:  x . "ab" . x  in  (ab)*  ,  x in (a|b)*
; This instance: d = "ab"  ->  SAT   (even length; x=eps -> ab, or x=ab -> ababab)

(set-logic QF_S)
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(set-info :category "crafted")
(set-info :source |Synthetic word-equation difficulty ladder, grounded in the data/backrefs.json regex corpus (resharp-node). Encoding: a backreference becomes a REPEATED string variable; a lookaround becomes a membership constraint (positive = & = conjoined str.in_re; negative-over-backref = ~ = not str.contains). Statuses verified by brute force + parity/length arguments.|)
(declare-fun x () String)

(assert (str.in_re x (re.* (re.union (str.to_re "a") (str.to_re "b")))))
(assert (str.in_re (str.++ x "ab" x) (re.* (str.to_re "ab"))))

(check-sat)
