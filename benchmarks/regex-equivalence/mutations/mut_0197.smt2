;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance07268.smt2
;; Mutations:  bound_lower_dec, literal_char_inc, opt_to_required
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
;; R2: mutated (bound_lower_dec, literal_char_inc, opt_to_required)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.opt (re.union (str.to_re "+") (str.to_re "-"))) (re.+ (re.range "0" "9")) (re.opt (re.++ (str.to_re ",") ((_ re.loop 2 2) (re.range "0" "9")))) (re.* (str.to_re " ")) (str.to_re "\u{a}")) (re.comp (re.++ re.union (str.to_re "+") (str.to_re "-")) (re.+ (re.range "0" "9")) (re.opt (re.++ (str.to_re "-") ((_ re.loop 1 2) (re.range "0" "9")))) (re.* (str.to_re " ")) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.opt (re.union (str.to_re "+") (str.to_re "-"))) (re.+ (re.range "0" "9")) (re.opt (re.++ (str.to_re ",") ((_ re.loop 2 2) (re.range "0" "9")))) (re.* (str.to_re " ")) (str.to_re "\u{a}"))) (re.++ re.union (str.to_re "+") (str.to_re "-")) (re.+ (re.range "0" "9")) (re.opt (re.++ (str.to_re "-") ((_ re.loop 1 2) (re.range "0" "9")))) (re.* (str.to_re " ")) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
