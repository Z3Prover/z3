;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00735.smt2
;; Mutations:  range_expand_hi, range_shrink_lo, literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_expand_hi, range_shrink_lo, literal_char_dec)
(assert
  (not
    (=
      (re.++ (str.to_re "/i=") ((_ re.loop 40 40) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9") (str.to_re "$") (str.to_re "~"))) (str.to_re "/U\u{a}"))
      (re.++ (str.to_re "/i<") ((_ re.loop 40 40) (re.union (re.range "b" "z") (re.range "A" "[") (re.range "0" "9") (str.to_re "$") (str.to_re "~"))) (str.to_re "/U\u{a}")))))

(check-sat)
(exit)
