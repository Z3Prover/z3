;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance06449.smt2
;; Mutations:  literal_char_inc, literal_char_inc, range_expand_hi
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_inc, literal_char_inc, range_expand_hi)
(assert
  (not
    (=
      (re.++ (re.+ (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9") (str.to_re "_") (str.to_re "-") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "\u{a}"))
      (re.++ (re.+ (re.union (re.range "a" "{") (re.range "A" "Z") (re.range "0" "9") (str.to_re "`") (str.to_re ".") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
