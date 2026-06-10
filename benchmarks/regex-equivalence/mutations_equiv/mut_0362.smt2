;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance02887.smt2
;; Mutations:  literal_char_dec, literal_char_dec, intersect_no_at_sign
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_dec, literal_char_dec, intersect_no_at_sign)
(assert
  (not
    (=
      (re.++ (re.+ (re.range "0" "9")) (re.* (str.to_re " ")) (re.opt (re.++ (re.union (str.to_re "p") (str.to_re "P")) (re.union (str.to_re "x") (str.to_re "X") (str.to_re "t") (str.to_re "T")))) (str.to_re "\u{a}"))
      (re.++ (re.+ (re.range "0" "9")) (re.inter (re.* (str.to_re " ")) (re.comp (re.++ re.all (str.to_re "@") re.all))) (re.opt (re.++ (re.union (str.to_re "p") (str.to_re "P")) (re.union (str.to_re "w") (str.to_re "X") (str.to_re "s") (str.to_re "T")))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
