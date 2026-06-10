;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance03817.smt2
;; Mutations:  literal_char_dec, range_expand_hi
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_dec, range_expand_hi)
(assert
  (not
    (=
      (re.++ (re.+ (re.range "0" "9")) (re.opt (re.union (str.to_re ".") (str.to_re ","))) (str.to_re "\u{a}"))
      (re.++ (re.+ (re.range "0" ":")) (re.opt (re.union (str.to_re "-") (str.to_re ","))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
