;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance03617.smt2
;; Mutations:  range_shrink_lo, bound_lower_dec, intersect_no_alnum3
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)

(declare-const x String)

;; R1: original
;; R2: mutated (range_shrink_lo, bound_lower_dec, intersect_no_alnum3)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.opt (re.union (str.to_re "V-") (str.to_re "I-"))) ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "\u{a}")) (re.comp (re.++ (re.inter (re.opt (re.union (str.to_re "V-") (str.to_re "I-"))) (re.comp (re.++ re.all ((_ re.loop 3 3) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) re.all))) ((_ re.loop 3 4) (re.range "1" "9")) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.opt (re.union (str.to_re "V-") (str.to_re "I-"))) ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "\u{a}"))) (re.++ (re.inter (re.opt (re.union (str.to_re "V-") (str.to_re "I-"))) (re.comp (re.++ re.all ((_ re.loop 3 3) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) re.all))) ((_ re.loop 3 4) (re.range "1" "9")) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
