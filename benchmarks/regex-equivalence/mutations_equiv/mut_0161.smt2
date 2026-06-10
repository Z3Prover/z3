;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance10835.smt2
;; Mutations:  literal_char_dec, literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_dec, literal_char_inc)
(assert
  (not
    (=
      (re.++ (str.to_re "\u{a}0") (re.union (str.to_re "7") (str.to_re "8")) (re.union (str.to_re "2") (str.to_re "3") (str.to_re "4") (str.to_re "7")) ((_ re.loop 7 7) (re.range "0" "9")))
      (re.++ (str.to_re "\u{a}0") (re.union (str.to_re "7") (str.to_re "9")) (re.union (str.to_re "2") (str.to_re "3") (str.to_re "4") (str.to_re "6")) ((_ re.loop 7 7) (re.range "0" "9"))))))

(check-sat)
(exit)
