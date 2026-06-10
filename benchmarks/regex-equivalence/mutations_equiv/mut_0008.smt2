;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance08290.smt2
;; Mutations:  intersect_no_digits4, bound_upper_inc, literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_digits4, bound_upper_inc, literal_char_dec)
(assert
  (not
    (=
      (re.union (re.++ ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9"))) (re.++ ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "A" "Z"))) (re.++ ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9"))) (re.++ ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "A" "Z"))) (re.++ ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9"))) (str.to_re "}") (re.++ ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 2 2) (re.range "A" "Z"))) (re.++ ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 3 3) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 1 1) (re.range "0" "9"))) (re.++ ((_ re.loop 1 1) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 3 3) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "\u{a}")))
      (re.union (re.++ ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9"))) (re.++ ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "A" "Z"))) (re.++ ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9"))) (re.++ ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "A" "Z"))) (re.++ ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9"))) (str.to_re "}") (re.++ ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re ",") ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 2 2) (re.range "A" "Z"))) (re.++ ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 3 4) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 1 1) (re.range "0" "9"))) (re.inter (re.++ ((_ re.loop 1 1) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 3 3) (re.range "A" "Z")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "\u{a}")) (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all)))))))

(check-sat)
(exit)
