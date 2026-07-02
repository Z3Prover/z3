; D0  copy baseline  (difficulty: trivial; 1 var, occ 2, coupling none)
; Derived from: duplicate-line matcher  (^|\n)(.*)(\n\2)+
; Word equation:  x . '#' . x = "ab#ab"   (backreference \2 -> variable x repeated twice)
; Expected: sat  (unique split forces x = "ab")

(set-logic QF_S)
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(set-info :category "crafted")
(set-info :source |Synthetic word-equation difficulty ladder, grounded in the data/backrefs.json regex corpus (resharp-node). Encoding: a backreference becomes a REPEATED string variable; a lookaround becomes a membership constraint (positive = & = conjoined str.in_re; negative-over-backref = ~ = not str.contains). Statuses verified by brute force + parity/length arguments.|)
(declare-fun x () String)

(assert (= (str.++ x "#" x) "ab#ab"))

(check-sat)
