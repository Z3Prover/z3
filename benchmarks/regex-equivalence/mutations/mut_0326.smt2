;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance12674.smt2
;; Mutations:  range_expand_hi, union_to_inter
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
;; R2: mutated (range_expand_hi, union_to_inter)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.* (re.++ (re.union (re.++ (re.union (str.to_re "0") (str.to_re "1")) (re.range "0" "9")) (re.++ (re.union (str.to_re "0") (str.to_re "1") (str.to_re "2")) (re.range "0" "3"))) (str.to_re ":") (re.range "0" "5") (re.range "0" "9"))) (str.to_re "\u{a}")) (re.comp (re.++ (re.* (re.++ (re.union (re.++ (re.inter(str.to_re "0") (str.to_re "1")) (re.range "0" "9")) (re.++ (re.union (str.to_re "0") (str.to_re "1") (str.to_re "2")) (re.range "0" "4"))) (str.to_re ":") (re.range "0" "5") (re.range "0" "9"))) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.* (re.++ (re.union (re.++ (re.union (str.to_re "0") (str.to_re "1")) (re.range "0" "9")) (re.++ (re.union (str.to_re "0") (str.to_re "1") (str.to_re "2")) (re.range "0" "3"))) (str.to_re ":") (re.range "0" "5") (re.range "0" "9"))) (str.to_re "\u{a}"))) (re.++ (re.* (re.++ (re.union (re.++ (re.inter(str.to_re "0") (str.to_re "1")) (re.range "0" "9")) (re.++ (re.union (str.to_re "0") (str.to_re "1") (str.to_re "2")) (re.range "0" "4"))) (str.to_re ":") (re.range "0" "5") (re.range "0" "9"))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
