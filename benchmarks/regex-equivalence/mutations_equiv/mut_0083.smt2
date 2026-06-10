;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance10743.smt2
;; Mutations:  range_shrink_lo, bound_upper_inc, literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo, bound_upper_inc, literal_char_dec)
(assert
  (not
    (=
      (re.++ (str.to_re "replaceMobileNo,' ','','") (re.union (str.to_re "+44") (str.to_re "0044") (str.to_re "0")) (str.to_re "7") (re.range "4" "9") ((_ re.loop 8 8) (re.range "0" "9")) (str.to_re "'\u{a}"))
      (re.++ (str.to_re "replaceMobileNo,' ','',&") (re.union (str.to_re "+44") (str.to_re "0044") (str.to_re "0")) (str.to_re "7") (re.range "4" "9") ((_ re.loop 8 9) (re.range "1" "9")) (str.to_re "'\u{a}")))))

(check-sat)
(exit)
