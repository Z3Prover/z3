;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance05001.smt2
;; Mutations:  intersect_no_digits4, range_shrink_lo
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_digits4, range_shrink_lo)
(assert
  (not
    (=
      (re.++ (re.+ (re.union (re.range "0" "9") (str.to_re ","))) (str.to_re "'-") (re.union (re.range "0" "9") (re.++ (str.to_re "1") (re.union (str.to_re "0") (str.to_re "1")))) (str.to_re "\u{22}\u{a}"))
      (re.++ (re.+ (re.union (re.range "0" "9") (str.to_re ","))) (str.to_re "'-") (re.union (re.range "1" "9") (re.++ (str.to_re "1") (re.inter (re.union (str.to_re "0") (str.to_re "1")) (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all))))) (str.to_re "\u{22}\u{a}")))))

(check-sat)
(exit)
