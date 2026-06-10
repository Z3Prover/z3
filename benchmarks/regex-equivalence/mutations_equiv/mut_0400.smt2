;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance14454.smt2
;; Mutations:  range_expand_hi, range_expand_hi, intersect_no_upper2
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_expand_hi, range_expand_hi, intersect_no_upper2)
(assert
  (not
    (=
      (re.++ (str.to_re "/{\u{22}") ((_ re.loop 4 4) (re.union (re.range "a" "f") (re.range "0" "9"))) (str.to_re "\u{22}:\u{22}") (re.union ((_ re.loop 32 32) (re.union (re.range "a" "f") (re.range "0" "9"))) (str.to_re "false")) (str.to_re "\u{22},/smiP\u{a}"))
      (re.++ (re.inter (str.to_re "/{\u{22}") (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) ((_ re.loop 4 4) (re.union (re.range "a" "g") (re.range "0" "9"))) (str.to_re "\u{22}:\u{22}") (re.union ((_ re.loop 32 32) (re.union (re.range "a" "f") (re.range "0" ":"))) (str.to_re "false")) (str.to_re "\u{22},/smiP\u{a}")))))

(check-sat)
(exit)
