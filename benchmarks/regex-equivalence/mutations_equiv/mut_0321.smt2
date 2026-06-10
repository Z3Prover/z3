;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance06301.smt2
;; Mutations:  range_shrink_lo, intersect_min_len_5
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo, intersect_min_len_5)
(assert
  (not
    (=
      (re.++ (str.to_re "\u{a}") (re.union (re.++ (str.to_re "1") ((_ re.loop 2 2) (re.range "0" "9"))) (re.++ (str.to_re "22") (re.range "0" "3")) (re.++ (re.range "1" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.union (str.to_re "0") (str.to_re "1")) (re.range "0" "9")) (re.range "1" "9")) re.allchar (re.union (re.++ (str.to_re "1") ((_ re.loop 2 2) (re.range "0" "9"))) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "25") (re.range "0" "5")) (re.++ (re.range "1" "9") (re.range "0" "9")) (re.range "0" "9")) re.allchar (re.union (re.++ (str.to_re "1") ((_ re.loop 2 2) (re.range "0" "9"))) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "25") (re.range "0" "5")) (re.++ (re.range "1" "9") (re.range "0" "9")) (re.range "0" "9")) re.allchar (re.union (re.++ (str.to_re "1") ((_ re.loop 2 2) (re.range "0" "9"))) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "25") (re.range "0" "5")) (re.++ (re.range "1" "9") (re.range "0" "9")) (re.range "0" "9")))
      (re.++ (str.to_re "\u{a}") (re.union (re.++ (str.to_re "1") ((_ re.loop 2 2) (re.range "0" "9"))) (re.++ (str.to_re "22") (re.range "0" "3")) (re.++ (re.range "1" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.union (str.to_re "0") (str.to_re "1")) (re.range "0" "9")) (re.range "1" "9")) re.allchar (re.union (re.++ (str.to_re "1") ((_ re.loop 2 2) (re.range "0" "9"))) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "25") (re.range "0" "5")) (re.++ (re.range "1" "9") (re.range "0" "9")) (re.range "0" "9")) re.allchar (re.union (re.++ (str.to_re "1") (re.inter ((_ re.loop 2 2) (re.range "0" "9")) (re.++ ((_ re.loop 5 5) re.allchar) re.all))) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "25") (re.range "0" "5")) (re.++ (re.range "1" "9") (re.range "0" "9")) (re.range "0" "9")) re.allchar (re.union (re.++ (str.to_re "1") ((_ re.loop 2 2) (re.range "1" "9"))) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "25") (re.range "0" "5")) (re.++ (re.range "1" "9") (re.range "0" "9")) (re.range "0" "9"))))))

(check-sat)
(exit)
