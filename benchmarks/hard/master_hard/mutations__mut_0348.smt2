;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance05255.smt2
;; Mutations:  intersect_max_len_10, bound_lower_dec
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
;; R2: mutated (intersect_max_len_10, bound_lower_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "/version=") (re.union (str.to_re "\u{22}") (str.to_re "'")) ((_ re.loop 1024 1024) (re.union (str.to_re "\u{22}") (str.to_re "'"))) (str.to_re "/\u{a}")) (re.comp (re.++ (str.to_re "/version=") (re.union (str.to_re "\u{22}") (str.to_re "'")) ((_ re.loop 1023 1024) (re.union (str.to_re "\u{22}") (str.to_re "'"))) (re.inter (str.to_re "/\u{a}") ((_ re.loop 0 10) re.allchar))))) (re.inter (re.comp (re.++ (str.to_re "/version=") (re.union (str.to_re "\u{22}") (str.to_re "'")) ((_ re.loop 1024 1024) (re.union (str.to_re "\u{22}") (str.to_re "'"))) (str.to_re "/\u{a}"))) (re.++ (str.to_re "/version=") (re.union (str.to_re "\u{22}") (str.to_re "'")) ((_ re.loop 1023 1024) (re.union (str.to_re "\u{22}") (str.to_re "'"))) (re.inter (str.to_re "/\u{a}") ((_ re.loop 0 10) re.allchar)))))))

(check-sat)
(exit)
