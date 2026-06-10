;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance06728.smt2
;; Mutations:  star_to_plus, intersect_no_alnum3
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (star_to_plus, intersect_no_alnum3)
(assert
  (not
    (=
      (re.++ (str.to_re "/filename=") (re.* (re.comp (str.to_re "\u{a}"))) (str.to_re ".wmf/i\u{a}"))
      (re.++ (re.inter (str.to_re "/filename=") (re.comp (re.++ re.all ((_ re.loop 3 3) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) re.all))) (re.+ (re.comp (str.to_re "\u{a}"))) (str.to_re ".wmf/i\u{a}")))))

(check-sat)
(exit)
