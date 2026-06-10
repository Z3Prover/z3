;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance03514.smt2
;; Mutations:  intersect_min_len_5, intersect_no_slash_slash, literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_min_len_5, intersect_no_slash_slash, literal_char_dec)
(assert
  (not
    (=
      (re.++ (str.to_re "/filename=") (re.* (re.comp (str.to_re "\u{a}"))) (str.to_re ".vwr/i\u{a}"))
      (re.++ (str.to_re "/filename<") (re.inter (re.* (re.comp (str.to_re "\u{a}"))) (re.comp (re.++ re.all (str.to_re "//") re.all))) (re.inter (str.to_re ".vwr/i\u{a}") (re.++ ((_ re.loop 5 5) re.allchar) re.all))))))

(check-sat)
(exit)
