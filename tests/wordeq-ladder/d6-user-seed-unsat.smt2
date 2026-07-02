; D6  USER SEED, UNSAT by parity  (difficulty: hard; 2 vars, occ 2 each, coupling global-structural &)
; Derived from EXACTLY: (?:(?=^(ab)*$))(a*)(b*)(a|b)\2\1   with the (a|b) alternative fixed to 'a'.
; Body  (a*)(b*)(a|b)\2\1  ->  x . y . a . y . x   ;   x in a* , y in b*
; Lookahead (?=^(ab)*$)  ->  & : the whole word in (ab)*   [BINDING constraint]
; Body language a*b*(a|b)b*a*  ->  & : second membership (auto-satisfied by the term shape; shown for fidelity)
; Expected: UNSAT.  |x.y.a.y.x| = 2|x|+2|y|+1 is ALWAYS odd, but (ab)* has only even-length words.
; Consequence: the user's seed regex matches NO string (empty language).

(set-logic QF_S)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-info :category "crafted")
(set-info :source |Synthetic word-equation difficulty ladder, grounded in the data/backrefs.json regex corpus (resharp-node). Encoding: a backreference becomes a REPEATED string variable; a lookaround becomes a membership constraint (positive = & = conjoined str.in_re; negative-over-backref = ~ = not str.contains). Statuses verified by brute force + parity/length arguments.|)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun w () String)

(assert (str.in_re x (re.* (str.to_re "a"))))
(assert (str.in_re y (re.* (str.to_re "b"))))
(assert (= w (str.++ x y "a" y x)))
(assert (str.in_re w (re.* (str.to_re "ab"))))
(assert (str.in_re w (re.++ (re.* (str.to_re "a")) (re.* (str.to_re "b")) (re.union (str.to_re "a") (str.to_re "b")) (re.* (str.to_re "b")) (re.* (str.to_re "a")))))

(check-sat)
