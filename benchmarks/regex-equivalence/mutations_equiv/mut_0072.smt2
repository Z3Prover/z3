;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance04033.smt2
;; Mutations:  range_shrink_lo, range_expand_hi, range_shrink_lo
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo, range_expand_hi, range_shrink_lo)
(assert
  (not
    (=
      (re.++ (re.union (re.++ (re.+ (re.range "1" "9")) (re.* (re.range "0" "9"))) (re.++ (re.* (re.range "0" "9")) (re.union (str.to_re ".") (str.to_re ",")) (re.range "0" "9"))) (str.to_re "\u{a}"))
      (re.++ (re.union (re.++ (re.+ (re.range "1" "9")) (re.* (re.range "1" "9"))) (re.++ (re.* (re.range "0" ":")) (re.union (str.to_re ".") (str.to_re ",")) (re.range "1" "9"))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
