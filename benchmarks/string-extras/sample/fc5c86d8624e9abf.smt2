; origin: https://github.com/Z3Prover/z3test/tree/master/regressions : smt2/5731.smt2.disabled
(set-option :encoding ascii)
(declare-const s String)
(assert (str.in_re s
(re.inter
(re.+ ((_ re.loop 1 100000) (str.to_re "a")))
(re.comp (re.++ re.all (str.to_re "a"))))))
(check-sat)

(reset)

(set-option :encoding ascii)
(declare-const s String)
(assert (str.in_re s
(re.inter
(re.++  (re.* ((_ re.loop 0 100000) (str.to_re "a"))) (str.to_re "ab"))
(re.comp (re.++ re.all (str.to_re "b"))))))
(check-sat)

(reset)

(set-option :encoding unicode)
(declare-const s String)
(assert (str.in_re s
(re.inter
(re.+ ((_ re.loop 1 100000) (str.to_re "\u{4000}")))
(re.comp (re.++ re.all (str.to_re "\u{4000}"))))))
(check-sat)

(reset)

(set-option :encoding unicode)
(declare-const s String)
(assert (str.in_re s
(re.inter
(re.++  (re.* ((_ re.loop 0 100000) (str.to_re "a"))) (re.++ (str.to_re "a") (re.range "\u{200}" "\u{2555}")))
(re.comp (re.++ re.all (re.range "h" "\u{3000}"))))))
(check-sat)

(reset)
