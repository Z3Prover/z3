;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11931.smt2
;; Mutations:  range_shrink_lo, literal_char_dec, range_expand_hi
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo, literal_char_dec, range_expand_hi)
(assert
  (not
    (=
      (re.++ (re.union (re.++ (str.to_re "1") (re.range "0" "2")) (re.++ (re.opt (str.to_re "0")) (re.range "1" "9"))) (str.to_re ":\u{a}") (re.opt (re.range "0" "5")) (re.range "0" "9") (str.to_re " ") (re.union (str.to_re "AM") (str.to_re "PM")))
      (re.++ (re.union (re.++ (str.to_re "1") (re.range "0" "3")) (re.++ (re.opt (str.to_re "/")) (re.range "1" "9"))) (str.to_re ":\u{a}") (re.opt (re.range "1" "5")) (re.range "0" "9") (str.to_re " ") (re.union (str.to_re "AM") (str.to_re "PM"))))))

(check-sat)
(exit)
