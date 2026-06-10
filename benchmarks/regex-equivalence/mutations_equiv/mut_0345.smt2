;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance01750.smt2
;; Mutations:  literal_char_dec, intersect_ascii_printable_only, literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_dec, intersect_ascii_printable_only, literal_char_dec)
(assert
  (not
    (=
      (re.++ (str.to_re "/.hta") (re.union (str.to_re "?") (str.to_re "\u{5c}") (str.to_re "/")) (str.to_re "/smiU\u{a}"))
      (re.++ (str.to_re "/.hta") (re.union (str.to_re ">") (re.inter (str.to_re "\u{5c}") (re.* (re.range " " "~"))) (str.to_re ".")) (str.to_re "/smiU\u{a}")))))

(check-sat)
(exit)
