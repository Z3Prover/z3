;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance07720.smt2
;; Mutations:  intersect_no_upper2
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
;; R2: mutated (intersect_no_upper2)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ ((_ re.loop 5 5) (re.++ ((_ re.loop 2 2) (re.union (re.range "0" "9") (re.range "A" "F"))) (re.union (str.to_re ":") (str.to_re "-")))) ((_ re.loop 2 2) (re.union (re.range "0" "9") (re.range "A" "F"))) (str.to_re "\u{a}")) (re.comp (re.++ ((_ re.loop 5 5) (re.inter (re.++ ((_ re.loop 2 2) (re.union (re.range "0" "9") (re.range "A" "F"))) (re.union (str.to_re ":") (str.to_re "-"))) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all)))) ((_ re.loop 2 2) (re.union (re.range "0" "9") (re.range "A" "F"))) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ ((_ re.loop 5 5) (re.++ ((_ re.loop 2 2) (re.union (re.range "0" "9") (re.range "A" "F"))) (re.union (str.to_re ":") (str.to_re "-")))) ((_ re.loop 2 2) (re.union (re.range "0" "9") (re.range "A" "F"))) (str.to_re "\u{a}"))) (re.++ ((_ re.loop 5 5) (re.inter (re.++ ((_ re.loop 2 2) (re.union (re.range "0" "9") (re.range "A" "F"))) (re.union (str.to_re ":") (str.to_re "-"))) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all)))) ((_ re.loop 2 2) (re.union (re.range "0" "9") (re.range "A" "F"))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
