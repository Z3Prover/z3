; D2  tag nesting with complement  (difficulty: low; 2 vars, occ 2, coupling complement ~)
; Derived from: HTML/XML body  <([a-z]+)((?!</\1).)*</\1>
; Simplified: open marker 'o', close marker 'c'; name x; body B.  Match = o . x . B . c . x
; The negative lookahead (?!</\1) -> body must NOT contain the close token 'c'.x :
;    ~-coupling rendered as  (not (str.contains B (str.++ "c" x)))  (variable-coupled -> not a fixed re.comp)
; Expected: sat  (x="a", B="" -> "oaca")

(set-logic QF_S)
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(set-info :category "crafted")
(set-info :source |Synthetic word-equation difficulty ladder, grounded in the data/backrefs.json regex corpus (resharp-node). Encoding: a backreference becomes a REPEATED string variable; a lookaround becomes a membership constraint (positive = & = conjoined str.in_re; negative-over-backref = ~ = not str.contains). Statuses verified by brute force + parity/length arguments.|)
(declare-fun x () String)
(declare-fun B () String)
(declare-fun w () String)

(assert (str.in_re x (re.+ (re.union (str.to_re "a") (str.to_re "b")))))
(assert (str.in_re B (re.* (re.union (re.union (str.to_re "a") (str.to_re "b")) (str.to_re "c")))))
(assert (= w (str.++ "o" x B "c" x)))
(assert (not (str.contains B (str.++ "c" x))))

(check-sat)
