;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance05990.smt2
;; Mutations:  star_to_plus, intersect_no_dot_dot, plus_to_star
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (star_to_plus, intersect_no_dot_dot, plus_to_star)
(assert
  (not
    (=
      (re.++ (str.to_re "\u{a}") (re.+ re.allchar) (re.+ (re.range "0" "9")) (re.* re.allchar))
      (re.++ (str.to_re "\u{a}") (re.* re.allchar) (re.inter (re.+ (re.range "0" "9")) (re.comp (re.++ re.all (str.to_re "..") re.all))) (re.+ re.allchar)))))

(check-sat)
(exit)
