;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance13810.smt2
;; Mutations:  bound_lower_dec, range_expand_hi, opt_to_required
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)

(declare-const x String)

;; R1: original
;; R2: mutated (bound_lower_dec, range_expand_hi, opt_to_required)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.opt (re.++ (re.opt (str.to_re "+")) (str.to_re "420"))) (re.opt (str.to_re " ")) ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re " ")) ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re " ")) ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "\u{a}")) (re.comp (re.++ (re.opt (re.++ (re.opt (str.to_re "+")) (str.to_re "420"))) str.to_re " ") ((_ re.loop 3 3) (re.range "0" ":")) (re.opt (str.to_re " ")) ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re " ")) ((_ re.loop 2 3) (re.range "0" "9")) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.opt (re.++ (re.opt (str.to_re "+")) (str.to_re "420"))) (re.opt (str.to_re " ")) ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re " ")) ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re " ")) ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "\u{a}"))) (re.++ (re.opt (re.++ (re.opt (str.to_re "+")) (str.to_re "420"))) str.to_re " ") ((_ re.loop 3 3) (re.range "0" ":")) (re.opt (str.to_re " ")) ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re " ")) ((_ re.loop 2 3) (re.range "0" "9")) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
