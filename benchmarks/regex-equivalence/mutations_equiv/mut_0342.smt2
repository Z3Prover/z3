;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance04540.smt2
;; Mutations:  literal_char_inc, range_expand_hi, opt_to_required
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_inc, range_expand_hi, opt_to_required)
(assert
  (not
    (=
      (re.++ (re.opt (str.to_re "1 ")) ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re " ") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "\u{a}"))
      (re.++ str.to_re "1 "))))

(check-sat)
(exit)
