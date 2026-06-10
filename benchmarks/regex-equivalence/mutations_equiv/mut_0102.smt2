;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11663.smt2
;; Mutations:  intersect_no_alnum5, star_to_plus
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_alnum5, star_to_plus)
(assert
  (not
    (=
      (re.++ (str.to_re "<img") (re.* (re.comp (str.to_re ">"))) (str.to_re " src=\u{22}") (re.* (re.comp (str.to_re "\u{22}"))) (str.to_re "\u{22}") (re.* (re.comp (str.to_re ">"))) (str.to_re ">\u{a}"))
      (re.++ (str.to_re "<img") (re.+ (re.comp (str.to_re ">"))) (str.to_re " src=\u{22}") (re.* (re.comp (re.inter (str.to_re "\u{22}") (re.comp (re.++ re.all ((_ re.loop 5 5) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) re.all))))) (str.to_re "\u{22}") (re.* (re.comp (str.to_re ">"))) (str.to_re ">\u{a}")))))

(check-sat)
(exit)
