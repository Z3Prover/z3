;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance05629.smt2
;; Mutations:  intersect_max_len_20
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
;; R2: mutated (intersect_max_len_20)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.range "\u{80}" "\u{ff}") (str.to_re "\u{a}")) (re.comp (re.++ (re.inter (re.range "\u{80}" "\u{ff}") ((_ re.loop 0 20) re.allchar)) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.range "\u{80}" "\u{ff}") (str.to_re "\u{a}"))) (re.++ (re.inter (re.range "\u{80}" "\u{ff}") ((_ re.loop 0 20) re.allchar)) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
