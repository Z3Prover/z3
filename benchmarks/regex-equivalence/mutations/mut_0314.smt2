;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance02524.smt2
;; Mutations:  literal_char_inc, intersect_no_upper2, literal_char_inc
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
;; R2: mutated (literal_char_inc, intersect_no_upper2, literal_char_inc)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "/.asx") (re.union (str.to_re "?") (str.to_re "\u{5c}") (str.to_re "/")) (str.to_re "/smiU\u{a}")) (re.comp (re.++ (str.to_re "/.asx") (re.union (str.to_re "@") (re.inter (str.to_re "\u{5c}") (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) (str.to_re "0")) (str.to_re "/smiU\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "/.asx") (re.union (str.to_re "?") (str.to_re "\u{5c}") (str.to_re "/")) (str.to_re "/smiU\u{a}"))) (re.++ (str.to_re "/.asx") (re.union (str.to_re "@") (re.inter (str.to_re "\u{5c}") (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) (str.to_re "0")) (str.to_re "/smiU\u{a}"))))))

(check-sat)
(exit)
