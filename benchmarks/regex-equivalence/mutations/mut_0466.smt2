;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance01993.smt2
;; Mutations:  range_expand_hi
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
;; R2: mutated (range_expand_hi)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "/.php?hgfc=") (re.+ (re.union (re.range "a" "f") (re.range "0" "9"))) (str.to_re "/U\u{a}")) (re.comp (re.++ (str.to_re "/.php?hgfc=") (re.+ (re.union (re.range "a" "g") (re.range "0" "9"))) (str.to_re "/U\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "/.php?hgfc=") (re.+ (re.union (re.range "a" "f") (re.range "0" "9"))) (str.to_re "/U\u{a}"))) (re.++ (str.to_re "/.php?hgfc=") (re.+ (re.union (re.range "a" "g") (re.range "0" "9"))) (str.to_re "/U\u{a}"))))))

(check-sat)
(exit)
