;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00840.smt2
;; Mutations:  union_to_inter, bound_lower_inc
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
;; R2: mutated (union_to_inter, bound_lower_inc)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ ((_ re.loop 1 10) (re.union re.allchar (str.to_re "\u{d}") (str.to_re "\u{a}"))) (str.to_re "\u{a}")) (re.comp (re.++ ((_ re.loop 2 10) (re.interre.allchar (str.to_re "\u{d}") (str.to_re "\u{a}"))) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ ((_ re.loop 1 10) (re.union re.allchar (str.to_re "\u{d}") (str.to_re "\u{a}"))) (str.to_re "\u{a}"))) (re.++ ((_ re.loop 2 10) (re.interre.allchar (str.to_re "\u{d}") (str.to_re "\u{a}"))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
