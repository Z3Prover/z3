;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance06251.smt2
;; Mutations:  plus_to_star, union_to_inter, union_to_inter
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (plus_to_star, union_to_inter, union_to_inter)
(assert
  (not
    (=
      (re.++ (str.to_re "/hwid=") (re.+ (re.union (str.to_re "\u{a}") (str.to_re "&"))) (str.to_re "&pc=") (re.+ (re.union (str.to_re "\u{a}") (str.to_re "&"))) (str.to_re "&localip=") (re.+ (re.union (str.to_re "\u{a}") (str.to_re "&"))) (str.to_re "&winver=/U\u{a}"))
      (re.++ (str.to_re "/hwid=") (re.+ (re.inter (str.to_re "\u{a}") (str.to_re "&"))) (str.to_re "&pc=") (re.+ (re.inter (str.to_re "\u{a}") (str.to_re "&"))) (str.to_re "&localip=") (re.* (re.union (str.to_re "\u{a}") (str.to_re "&"))) (str.to_re "&winver=/U\u{a}")))))

(check-sat)
(exit)
