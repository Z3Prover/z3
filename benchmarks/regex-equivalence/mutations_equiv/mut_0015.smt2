;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance06543.smt2
;; Mutations:  union_to_inter, range_shrink_hi
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (union_to_inter, range_shrink_hi)
(assert
  (not
    (=
      (re.++ (str.to_re "/guid=") ((_ re.loop 32 32) (re.union (re.range "a" "f") (re.range "0" "9"))) (str.to_re "&state=") (re.union (str.to_re "LOST") (str.to_re "WORK") (str.to_re "WAIT") (str.to_re "RUN")) (str.to_re "/P\u{a}"))
      (re.++ (str.to_re "/guid=") ((_ re.loop 32 32) (re.union (re.range "a" "e") (re.range "0" "9"))) (str.to_re "&state=") (re.inter (str.to_re "LOST") (str.to_re "WORK") (str.to_re "WAIT") (str.to_re "RUN")) (str.to_re "/P\u{a}")))))

(check-sat)
(exit)
