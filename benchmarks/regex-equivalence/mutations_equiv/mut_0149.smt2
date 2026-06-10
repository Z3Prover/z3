;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance05634.smt2
;; Mutations:  range_expand_hi, literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_expand_hi, literal_char_inc)
(assert
  (not
    (=
      (re.++ (str.to_re "on") (re.range "0" "9") (str.to_re "stepwww.kornputers.com\u{a}"))
      (re.++ (str.to_re "oo") (re.range "0" ":") (str.to_re "stepwww.kornputers.com\u{a}")))))

(check-sat)
(exit)
