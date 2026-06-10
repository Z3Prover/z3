;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance12579.smt2
;; Mutations:  literal_char_inc, range_shrink_lo
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_inc, range_shrink_lo)
(assert
  (not
    (=
      (re.++ (str.to_re "/i=") ((_ re.loop 40 40) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9") (str.to_re "$") (str.to_re "~"))) (str.to_re "/U\u{a}"))
      (re.++ (str.to_re "/i=") ((_ re.loop 40 40) (re.union (re.range "b" "z") (re.range "A" "Z") (re.range "0" "9") (str.to_re "%") (str.to_re "~"))) (str.to_re "/U\u{a}")))))

(check-sat)
(exit)
