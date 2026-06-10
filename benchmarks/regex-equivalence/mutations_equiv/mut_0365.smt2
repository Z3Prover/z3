;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance03368.smt2
;; Mutations:  intersect_ascii_printable_only, range_shrink_lo, literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_ascii_printable_only, range_shrink_lo, literal_char_inc)
(assert
  (not
    (=
      (re.++ (str.to_re "Host:") (re.range "0" "9") (str.to_re "ATTENTION:") (re.* re.allchar) (str.to_re "User-Agent:\u{a}"))
      (re.++ (str.to_re "Host;") (re.range "1" "9") (str.to_re "ATTENTION:") (re.* re.allchar) (re.inter (str.to_re "User-Agent:\u{a}") (re.* (re.range " " "~")))))))

(check-sat)
(exit)
