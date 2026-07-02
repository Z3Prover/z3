; D8  counting / Parikh coupling  (difficulty axis: LENGTH not content; 2 vars)
; Derived from: Rust raw string  b?r(#*)"..."\1  and markdown fence  (`+)...\1  (run lengths must match).
; Simplified: opening #-run x (backref \1 forces closing run = x, same variable); content M; quotes 'q'.
; Match = r . x . q . M . q . x   with a linear length coupling |M| = 3*|x|  (Parikh-style).
; Expected: sat  (x="#", M="aaa" -> |M|=3=3*1). Add stronger length constraints to scale to Presburger-hard.

(set-logic QF_SLIA)
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(set-info :category "crafted")
(set-info :source |Synthetic word-equation difficulty ladder, grounded in the data/backrefs.json regex corpus (resharp-node). Encoding: a backreference becomes a REPEATED string variable; a lookaround becomes a membership constraint (positive = & = conjoined str.in_re; negative-over-backref = ~ = not str.contains). Statuses verified by brute force + parity/length arguments.|)
(declare-fun x () String)
(declare-fun M () String)
(declare-fun w () String)

(assert (str.in_re x (re.* (str.to_re "#"))))
(assert (str.in_re M (re.* (re.union (str.to_re "a") (str.to_re "b")))))
(assert (= w (str.++ "r" x "q" M "q" x)))
(assert (>= (str.len x) 1))
(assert (= (str.len M) (* 3 (str.len x))))

(check-sat)
