; D7  cube / high multiplicity  (difficulty: medium-hard; 1 var, occ 3, coupling global-structural &)
; Derived from: nested-tag matchers where the tag-name backreference \1 occurs 4x.
; Word equation:  x . x . x  in  (ab)*  ,  x in (a|b)+
; Expected: sat  (x="ab" -> ababab). Stresses repeated-variable multiplicity.

(set-logic QF_S)
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(set-info :category "crafted")
(set-info :source |Synthetic word-equation difficulty ladder, grounded in the data/backrefs.json regex corpus (resharp-node). Encoding: a backreference becomes a REPEATED string variable; a lookaround becomes a membership constraint (positive = & = conjoined str.in_re; negative-over-backref = ~ = not str.contains). Statuses verified by brute force + parity/length arguments.|)
(declare-fun x () String)

(assert (str.in_re x (re.+ (re.union (str.to_re "a") (str.to_re "b")))))
(assert (str.in_re (str.++ x x x) (re.* (str.to_re "ab"))))

(check-sat)
