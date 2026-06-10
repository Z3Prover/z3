;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00580.smt2
;; Mutations:  opt_to_required
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (opt_to_required)
(assert
  (not
    (=
      (re.++ (str.to_re "http") (re.opt (str.to_re "s")) (str.to_re "://") (re.+ (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9") (re.range "." "/"))) (str.to_re "\u{a}"))
      (re.++ (str.to_re "http") str.to_re "s"))))

(check-sat)
(exit)
