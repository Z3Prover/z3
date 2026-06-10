;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00564.smt2
;; Mutations:  range_shrink_hi, range_shrink_lo, union_to_inter
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_hi, range_shrink_lo, union_to_inter)
(assert
  (not
    (=
      (re.++ (str.to_re "Host:") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "User-Agent:Host:\u{a}"))
      (re.++ (str.to_re "Host:") (re.+ (re.inter (re.range "1" "9") (re.range "A" "Y") (re.range "a" "z") (str.to_re "_"))) (str.to_re "User-Agent:Host:\u{a}")))))

(check-sat)
(exit)
