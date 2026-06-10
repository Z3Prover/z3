;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance06904.smt2
;; Mutations:  range_expand_hi, range_shrink_hi, opt_to_required
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
;; R2: mutated (range_expand_hi, range_shrink_hi, opt_to_required)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.union (re.++ (re.opt (re.union (re.range "a" "z") (str.to_re "'"))) (re.* (re.union (re.range "a" "z") (str.to_re "'") (str.to_re " ")))) (re.++ (re.opt (re.++ (re.range "a" "z") (str.to_re "."))) (re.range "a" "z") (str.to_re "."))) (str.to_re "\u{a}")) (re.comp (re.++ (re.union (re.++ re.union (re.range "a" "z") (str.to_re "'")) (re.* (re.union (re.range "a" "y") (str.to_re "'") (str.to_re " ")))) (re.++ (re.opt (re.++ (re.range "a" "z") (str.to_re "."))) (re.range "a" "{") (str.to_re "."))) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.union (re.++ (re.opt (re.union (re.range "a" "z") (str.to_re "'"))) (re.* (re.union (re.range "a" "z") (str.to_re "'") (str.to_re " ")))) (re.++ (re.opt (re.++ (re.range "a" "z") (str.to_re "."))) (re.range "a" "z") (str.to_re "."))) (str.to_re "\u{a}"))) (re.++ (re.union (re.++ re.union (re.range "a" "z") (str.to_re "'")) (re.* (re.union (re.range "a" "y") (str.to_re "'") (str.to_re " ")))) (re.++ (re.opt (re.++ (re.range "a" "z") (str.to_re "."))) (re.range "a" "{") (str.to_re "."))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
