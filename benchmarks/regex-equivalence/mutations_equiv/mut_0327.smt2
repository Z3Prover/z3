;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance10544.smt2
;; Mutations:  range_shrink_lo
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo)
(assert
  (not
    (=
      (re.++ (re.+ (re.range "0" "9")) (str.to_re ".") (re.range "0" "9") (str.to_re ".") (re.range "0" "9") (re.union (str.to_re "0") (str.to_re "1")) (re.range "0" "9") (re.range "0" "3") (re.range "0" "9") (str.to_re ".") (re.range "1" "9") (re.* (re.range "0" "9")) (str.to_re "\u{a}"))
      (re.++ (re.+ (re.range "0" "9")) (str.to_re ".") (re.range "0" "9") (str.to_re ".") (re.range "0" "9") (re.union (str.to_re "0") (str.to_re "1")) (re.range "1" "9") (re.range "0" "3") (re.range "0" "9") (str.to_re ".") (re.range "1" "9") (re.* (re.range "0" "9")) (str.to_re "\u{a}")))))

(check-sat)
(exit)
