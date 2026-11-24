; origin: https://github.com/Z3Prover/z3test/tree/master/regressions : smt2/5724.smt2
(set-option :encoding ascii)
(declare-fun X () String)
(assert (not (str.in.re X (re.* (re.union (re.range "\u{0}" "\u{7F}") (re.range "\u{80}" "\u{FF}"))))))
(check-sat)

(reset)

(set-option :encoding ascii)
(declare-fun X () String)
(assert (not (str.in.re X (re.* (re.union (re.range "\u{0}" "\u{8F}") (re.range "\u{80}" "\u{FF}"))))))
(check-sat)

(reset)

(set-option :encoding unicode)
(declare-fun X () String)
(assert (not (str.in.re X (re.* (re.union (re.range "\u{0}" "\u{3fff}") (re.range "\u{4000}" "\u{2FFFF}"))))))
(check-sat)

(reset)

(set-option :encoding unicode)
(declare-fun X () String)
(assert (not (str.in.re X (re.* (re.union (re.range "\u{0}" "\u{400}") (re.range "\u{200}" "\u{2FFFF}"))))))
(check-sat)

(reset)
