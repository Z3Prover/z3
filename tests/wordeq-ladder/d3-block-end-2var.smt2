; D3  two-variable existence coupling  (difficulty: medium; 2 vars, occ 2 each; richest REAL shape)
; Derived from: VB block matcher  ^([\t ]*)(\w+).*?\n\1End\2   (couples indent \1 AND name \2)
; Simplified: indent i over {s,t}; name x over {a,b}; End marker 'e'; body M.
; Match = i . x . M . i . e . x   (i repeated twice, x repeated twice = two coupled backreferences)
; Non-greedy body .*? -> (not (str.contains M (str.++ i "e" x)))
; Expected: sat  (i="", x="a", M="" -> "aea")

(set-logic QF_S)
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(set-info :category "crafted")
(set-info :source |Synthetic word-equation difficulty ladder, grounded in the data/backrefs.json regex corpus (resharp-node). Encoding: a backreference becomes a REPEATED string variable; a lookaround becomes a membership constraint (positive = & = conjoined str.in_re; negative-over-backref = ~ = not str.contains). Statuses verified by brute force + parity/length arguments.|)
(declare-fun i () String)
(declare-fun x () String)
(declare-fun M () String)
(declare-fun w () String)

(assert (str.in_re i (re.* (re.union (str.to_re "s") (str.to_re "t")))))
(assert (str.in_re x (re.+ (re.union (str.to_re "a") (str.to_re "b")))))
(assert (str.in_re M (re.* (re.union (re.union (str.to_re "a") (str.to_re "b")) (re.union (str.to_re "e") (re.union (str.to_re "s") (str.to_re "t")))))))
(assert (= w (str.++ i x M i "e" x)))
(assert (not (str.contains M (str.++ i "e" x))))

(check-sat)
