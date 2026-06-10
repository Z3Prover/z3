;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance06984.smt2
;; Mutations:  intersect_max_len_20, literal_char_inc
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
;; R2: mutated (intersect_max_len_20, literal_char_inc)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "/.wmv") (re.union (str.to_re "?") (str.to_re "\u{5c}") (str.to_re "/")) (str.to_re "/smiU\u{a}")) (re.comp (re.++ (str.to_re "/.wmv") (re.union (str.to_re "@") (str.to_re "\u{5c}") (str.to_re "/")) (re.inter (str.to_re "/smiU\u{a}") ((_ re.loop 0 20) re.allchar))))) (re.inter (re.comp (re.++ (str.to_re "/.wmv") (re.union (str.to_re "?") (str.to_re "\u{5c}") (str.to_re "/")) (str.to_re "/smiU\u{a}"))) (re.++ (str.to_re "/.wmv") (re.union (str.to_re "@") (str.to_re "\u{5c}") (str.to_re "/")) (re.inter (str.to_re "/smiU\u{a}") ((_ re.loop 0 20) re.allchar)))))))

(check-sat)
(exit)
