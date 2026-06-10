;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance02755.smt2
;; Mutations:  range_shrink_hi, union_to_inter, intersect_no_slash_slash
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
;; R2: mutated (range_shrink_hi, union_to_inter, intersect_no_slash_slash)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "/GET /3010") ((_ re.loop 166 166) (re.union (re.range "0" "9") (re.range "A" "F"))) (str.to_re "00000001/\u{a}")) (re.comp (re.++ (re.inter (str.to_re "/GET /3010") (re.comp (re.++ re.all (str.to_re "//") re.all))) ((_ re.loop 166 166) (re.inter(re.range "0" "8") (re.range "A" "F"))) (str.to_re "00000001/\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "/GET /3010") ((_ re.loop 166 166) (re.union (re.range "0" "9") (re.range "A" "F"))) (str.to_re "00000001/\u{a}"))) (re.++ (re.inter (str.to_re "/GET /3010") (re.comp (re.++ re.all (str.to_re "//") re.all))) ((_ re.loop 166 166) (re.inter(re.range "0" "8") (re.range "A" "F"))) (str.to_re "00000001/\u{a}"))))))

(check-sat)
(exit)
