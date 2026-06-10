;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00121.smt2
;; Mutations:  intersect_no_at_sign, star_to_plus
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_at_sign, star_to_plus)
(assert
  (not
    (=
      (re.++ (re.* (re.union (str.to_re "\u{5c}") (str.to_re "/") (str.to_re "?") (str.to_re "*") (str.to_re "\u{22}") (str.to_re ">") (str.to_re "<") (str.to_re ":") (str.to_re "|"))) (str.to_re "\u{a}"))
      (re.++ (re.+ (re.inter (re.union (str.to_re "\u{5c}") (str.to_re "/") (str.to_re "?") (str.to_re "*") (str.to_re "\u{22}") (str.to_re ">") (str.to_re "<") (str.to_re ":") (str.to_re "|")) (re.comp (re.++ re.all (str.to_re "@") re.all)))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
