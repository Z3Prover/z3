;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00066.smt2
;; Mutations:  range_shrink_hi, literal_char_dec, range_expand_hi
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_hi, literal_char_dec, range_expand_hi)
(assert
  (not
    (=
      (re.++ ((_ re.loop 5 5) (re.range "0" "9")) (re.opt (re.++ ((_ re.loop 1 1) (str.to_re "-")) ((_ re.loop 4 4) (re.range "0" "9")))) (str.to_re "\u{a}"))
      (re.++ ((_ re.loop 5 5) (re.range "0" ":")) (re.opt (re.++ ((_ re.loop 1 1) (str.to_re ",")) ((_ re.loop 4 4) (re.range "0" "8")))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
