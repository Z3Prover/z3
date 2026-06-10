;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11088.smt2
;; Mutations:  range_shrink_hi, range_shrink_lo, intersect_max_len_10
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_hi, range_shrink_lo, intersect_max_len_10)
(assert
  (not
    (=
      (re.++ (re.union (str.to_re "\u{5c}") (str.to_re "\u{22}") (str.to_re "=") (str.to_re "/") (str.to_re ">")) (re.union (re.++ (str.to_re "25") (re.range "0" "4")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "1") ((_ re.loop 2 2) (re.range "0" "9"))) ((_ re.loop 2 2) (re.range "0" "9"))) (str.to_re ".") ((_ re.loop 2 2) (re.++ (re.union (re.++ (str.to_re "25") (re.range "0" "4")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "1") ((_ re.loop 2 2) (re.range "0" "9"))) ((_ re.loop 1 2) (re.range "0" "9"))) (str.to_re "."))) (re.union (re.++ (str.to_re "25") (re.range "0" "4")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "1") ((_ re.loop 2 2) (re.range "0" "9"))) ((_ re.loop 2 2) (re.range "0" "9")) (re.range "1" "9")) (re.union (str.to_re "\u{5c}") (str.to_re "\u{22}") (str.to_re "=") (str.to_re ":") (str.to_re ";") (str.to_re ",") (str.to_re "/") (str.to_re "<")) (str.to_re "\u{a}"))
      (re.++ (re.union (str.to_re "\u{5c}") (str.to_re "\u{22}") (str.to_re "=") (str.to_re "/") (str.to_re ">")) (re.union (re.++ (str.to_re "25") (re.range "0" "4")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.inter (re.++ (str.to_re "1") ((_ re.loop 2 2) (re.range "0" "9"))) ((_ re.loop 0 10) re.allchar)) ((_ re.loop 2 2) (re.range "0" "9"))) (str.to_re ".") ((_ re.loop 2 2) (re.++ (re.union (re.++ (str.to_re "25") (re.range "1" "4")) (re.++ (str.to_re "2") (re.range "0" "3") (re.range "0" "9")) (re.++ (str.to_re "1") ((_ re.loop 2 2) (re.range "0" "9"))) ((_ re.loop 1 2) (re.range "0" "9"))) (str.to_re "."))) (re.union (re.++ (str.to_re "25") (re.range "0" "4")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "1") ((_ re.loop 2 2) (re.range "0" "9"))) ((_ re.loop 2 2) (re.range "0" "9")) (re.range "1" "9")) (re.union (str.to_re "\u{5c}") (str.to_re "\u{22}") (str.to_re "=") (str.to_re ":") (str.to_re ";") (str.to_re ",") (str.to_re "/") (str.to_re "<")) (str.to_re "\u{a}")))))

(check-sat)
(exit)
