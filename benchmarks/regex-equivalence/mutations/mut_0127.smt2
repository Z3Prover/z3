;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance07942.smt2
;; Mutations:  range_shrink_lo, intersect_max_len_20
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
;; R2: mutated (range_shrink_lo, intersect_max_len_20)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 1 4) (re.range "0" "9")) (str.to_re "\u{a}")) (re.comp (re.++ (re.inter ((_ re.loop 1 3) (re.range "0" "9")) ((_ re.loop 0 20) re.allchar)) (str.to_re ".") ((_ re.loop 1 4) (re.range "1" "9")) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 1 4) (re.range "0" "9")) (str.to_re "\u{a}"))) (re.++ (re.inter ((_ re.loop 1 3) (re.range "0" "9")) ((_ re.loop 0 20) re.allchar)) (str.to_re ".") ((_ re.loop 1 4) (re.range "1" "9")) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
