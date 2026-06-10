;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00453.smt2
;; Mutations:  intersect_max_len_10
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
;; R2: mutated (intersect_max_len_10)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "cdpView") (re.* re.allchar) (str.to_re "protocol") (re.* re.allchar) (str.to_re "/s(robert@blackcastlesoft.com)\u{a}")) (re.comp (re.++ (str.to_re "cdpView") (re.* re.allchar) (re.inter (str.to_re "protocol") ((_ re.loop 0 10) re.allchar)) (re.* re.allchar) (str.to_re "/s(robert@blackcastlesoft.com)\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "cdpView") (re.* re.allchar) (str.to_re "protocol") (re.* re.allchar) (str.to_re "/s(robert@blackcastlesoft.com)\u{a}"))) (re.++ (str.to_re "cdpView") (re.* re.allchar) (re.inter (str.to_re "protocol") ((_ re.loop 0 10) re.allchar)) (re.* re.allchar) (str.to_re "/s(robert@blackcastlesoft.com)\u{a}"))))))

(check-sat)
(exit)
