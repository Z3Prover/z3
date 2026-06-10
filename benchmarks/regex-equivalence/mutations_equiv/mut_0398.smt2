;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11910.smt2
;; Mutations:  literal_char_dec, range_shrink_lo
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_dec, range_shrink_lo)
(assert
  (not
    (=
      (re.++ (re.range "a" "z") ((_ re.loop 5 31) (re.union (re.range "a" "z") (re.range "0" "9") (str.to_re ".") (str.to_re ",") (str.to_re "-") (str.to_re "_"))) (str.to_re "\u{a}"))
      (re.++ (re.range "a" "z") ((_ re.loop 5 31) (re.union (re.range "a" "z") (re.range "1" "9") (str.to_re ".") (str.to_re ",") (str.to_re ",") (str.to_re "_"))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
