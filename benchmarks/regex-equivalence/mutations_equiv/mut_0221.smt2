;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance15241.smt2
;; Mutations:  range_shrink_lo, literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo, literal_char_inc)
(assert
  (not
    (=
      (re.++ (str.to_re "/hello/") (re.range "0" "9") (str.to_re ".") (re.range "0" "9") (str.to_re "/") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "/") ((_ re.loop 8 8) (re.union (re.range "0" "9") (re.range "a" "f"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "0" "9") (re.range "a" "f"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "0" "9") (re.range "a" "f"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "0" "9") (re.range "a" "f"))) (str.to_re "-") ((_ re.loop 12 12) (re.union (re.range "0" "9") (re.range "a" "f"))) (str.to_re "/i\u{a}"))
      (re.++ (str.to_re "/hello0") (re.range "0" "9") (str.to_re ".") (re.range "0" "9") (str.to_re "/") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "/") ((_ re.loop 8 8) (re.union (re.range "0" "9") (re.range "a" "f"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "0" "9") (re.range "a" "f"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "0" "9") (re.range "a" "f"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "0" "9") (re.range "a" "f"))) (str.to_re "-") ((_ re.loop 12 12) (re.union (re.range "1" "9") (re.range "a" "f"))) (str.to_re "/i\u{a}")))))

(check-sat)
(exit)
