;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance05931.smt2
;; Mutations:  intersect_min_len_5, range_expand_hi
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
;; R2: mutated (intersect_min_len_5, range_expand_hi)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ ((_ re.loop 5 12) (re.union (re.range "A" "Z") (re.range "0" "9") (re.range "\u{5c}" "\u{5c}") (str.to_re "&") (str.to_re "-"))) (str.to_re "\u{a}")) (re.comp (re.++ ((_ re.loop 5 12) (re.union (re.range "A" "[") (re.range "0" "9") (re.inter (re.range "\u{5c}" "\u{5c}") (re.++ ((_ re.loop 5 5) re.allchar) re.all)) (str.to_re "&") (str.to_re "-"))) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ ((_ re.loop 5 12) (re.union (re.range "A" "Z") (re.range "0" "9") (re.range "\u{5c}" "\u{5c}") (str.to_re "&") (str.to_re "-"))) (str.to_re "\u{a}"))) (re.++ ((_ re.loop 5 12) (re.union (re.range "A" "[") (re.range "0" "9") (re.inter (re.range "\u{5c}" "\u{5c}") (re.++ ((_ re.loop 5 5) re.allchar) re.all)) (str.to_re "&") (str.to_re "-"))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
