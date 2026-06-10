;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00125.smt2
;; Mutations:  plus_to_star, plus_to_star
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (plus_to_star, plus_to_star)
(assert
  (not
    (=
      (re.++ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "\u{a}") (re.range "A" "Z") (re.+ (re.range "a" "z")) (re.range "A" "Z") (re.+ (re.union (re.range "a" "z") (re.range "A" "Z") (str.to_re "-"))))
      (re.++ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "\u{a}") (re.range "A" "Z") (re.* (re.range "a" "z")) (re.range "A" "Z") (re.* (re.union (re.range "a" "z") (re.range "A" "Z") (str.to_re "-")))))))

(check-sat)
(exit)
