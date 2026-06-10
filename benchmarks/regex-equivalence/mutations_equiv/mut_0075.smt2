;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance08846.smt2
;; Mutations:  intersect_no_spaces, literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_spaces, literal_char_dec)
(assert
  (not
    (=
      (re.++ (str.to_re "Subject:") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "www.searchwords.com\u{a}"))
      (re.++ (str.to_re "Subject9") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.inter (str.to_re "www.searchwords.com\u{a}") (re.comp (re.++ re.all (str.to_re " ") re.all)))))))

(check-sat)
(exit)
