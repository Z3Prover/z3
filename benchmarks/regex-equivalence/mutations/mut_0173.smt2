;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance04102.smt2
;; Mutations:  range_expand_hi, range_expand_hi
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
;; R2: mutated (range_expand_hi, range_expand_hi)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ ((_ re.loop 1 1) (re.union (re.range "A" "Z") (re.range "a" "z"))) ((_ re.loop 7 7) (re.range "0" "9")) (str.to_re "\u{a}")) (re.comp (re.++ ((_ re.loop 1 1) (re.union (re.range "A" "[") (re.range "a" "{"))) ((_ re.loop 7 7) (re.range "0" "9")) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ ((_ re.loop 1 1) (re.union (re.range "A" "Z") (re.range "a" "z"))) ((_ re.loop 7 7) (re.range "0" "9")) (str.to_re "\u{a}"))) (re.++ ((_ re.loop 1 1) (re.union (re.range "A" "[") (re.range "a" "{"))) ((_ re.loop 7 7) (re.range "0" "9")) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
