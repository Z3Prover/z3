;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance02960.smt2
;; Mutations:  intersect_min_len_5, union_to_inter, literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_min_len_5, union_to_inter, literal_char_dec)
(assert
  (not
    (=
      (re.++ (str.to_re "Host:") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "upgrade.qsrch.infox2Fie.aspdcww.dmcast.com\u{a}"))
      (re.++ (str.to_re "Host9") (re.inter (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.inter (str.to_re "upgrade.qsrch.infox2Fie.aspdcww.dmcast.com\u{a}") (re.++ ((_ re.loop 5 5) re.allchar) re.all))))))

(check-sat)
(exit)
