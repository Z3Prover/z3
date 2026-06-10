;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11697.smt2
;; Mutations:  opt_to_required
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
;; R2: mutated (opt_to_required)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.opt (str.to_re "-")) (re.union (re.++ (re.opt (str.to_re "1")) (re.range "1" "7") (re.range "1" "9")) (re.++ (re.opt (str.to_re "1")) (re.range "1" "8") (str.to_re "0")) (re.++ (re.opt (re.range "1" "9")) (re.range "0" "9"))) ((_ re.loop 1 1) (str.to_re ".")) ((_ re.loop 1 6) (re.range "0" "9")) (str.to_re "\u{a}")) (re.comp (re.++ (re.opt (str.to_re "-")) (re.union (re.++ str.to_re "1") (re.range "1" "7") (re.range "1" "9")) (re.++ (re.opt (str.to_re "1")) (re.range "1" "8") (str.to_re "0")) (re.++ (re.opt (re.range "1" "9")) (re.range "0" "9"))) ((_ re.loop 1 1) (str.to_re ".")) ((_ re.loop 1 6) (re.range "0" "9")) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.opt (str.to_re "-")) (re.union (re.++ (re.opt (str.to_re "1")) (re.range "1" "7") (re.range "1" "9")) (re.++ (re.opt (str.to_re "1")) (re.range "1" "8") (str.to_re "0")) (re.++ (re.opt (re.range "1" "9")) (re.range "0" "9"))) ((_ re.loop 1 1) (str.to_re ".")) ((_ re.loop 1 6) (re.range "0" "9")) (str.to_re "\u{a}"))) (re.++ (re.opt (str.to_re "-")) (re.union (re.++ str.to_re "1") (re.range "1" "7") (re.range "1" "9")) (re.++ (re.opt (str.to_re "1")) (re.range "1" "8") (str.to_re "0")) (re.++ (re.opt (re.range "1" "9")) (re.range "0" "9"))) ((_ re.loop 1 1) (str.to_re ".")) ((_ re.loop 1 6) (re.range "0" "9")) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
