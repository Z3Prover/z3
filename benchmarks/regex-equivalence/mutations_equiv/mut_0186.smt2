;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance01648.smt2
;; Mutations:  range_expand_hi, union_to_inter, literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_expand_hi, union_to_inter, literal_char_dec)
(assert
  (not
    (=
      (re.++ (str.to_re "/") ((_ re.loop 8 8) (re.union (re.range "0" "9") (re.range "A" "Z"))) (str.to_re ":bpass\u{a}/\u{a}"))
      (re.++ (str.to_re ".") ((_ re.loop 8 8) (re.inter (re.range "0" ":") (re.range "A" "Z"))) (str.to_re ":bpass\u{a}/\u{a}")))))

(check-sat)
(exit)
