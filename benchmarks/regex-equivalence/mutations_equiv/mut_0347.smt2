;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance15640.smt2
;; Mutations:  intersect_no_alnum3
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_alnum3)
(assert
  (not
    (=
      (re.++ (str.to_re "/<linearGradient") (re.* (re.comp (str.to_re ">"))) (str.to_re ">") (re.* (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "</linearGradient>/i\u{a}"))
      (re.++ (str.to_re "/<linearGradient") (re.inter (re.* (re.comp (str.to_re ">"))) (re.comp (re.++ re.all ((_ re.loop 3 3) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) re.all))) (str.to_re ">") (re.* (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "</linearGradient>/i\u{a}")))))

(check-sat)
(exit)
