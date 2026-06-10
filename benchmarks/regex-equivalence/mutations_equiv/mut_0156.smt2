;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance12852.smt2
;; Mutations:  intersect_max_len_10, literal_char_inc, union_to_inter
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_max_len_10, literal_char_inc, union_to_inter)
(assert
  (not
    (=
      (re.++ (str.to_re "/agent_") (re.union (str.to_re "win") (str.to_re "lin") (str.to_re "mac")) (str.to_re "_helper.jar/siU\u{a}"))
      (re.++ (str.to_re "/agent_") (re.inter (str.to_re "win") (str.to_re "lin") (str.to_re "mad")) (re.inter (str.to_re "_helper.jar/siU\u{a}") ((_ re.loop 0 10) re.allchar))))))

(check-sat)
(exit)
