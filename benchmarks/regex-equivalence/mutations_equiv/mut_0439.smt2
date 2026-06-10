;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance02877.smt2
;; Mutations:  union_to_inter
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (union_to_inter)
(assert
  (not
    (=
      (re.++ (str.to_re "SI|Server|\u{13}") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "OSSProxy\u{5c}home/lordofsearch%3fAuthorization:\u{a}"))
      (re.++ (str.to_re "SI|Server|\u{13}") (re.+ (re.inter (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "OSSProxy\u{5c}home/lordofsearch%3fAuthorization:\u{a}")))))

(check-sat)
(exit)
