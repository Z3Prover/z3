;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance02344.smt2
;; Mutations:  literal_char_inc, literal_char_dec, union_to_inter
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
;; R2: mutated (literal_char_inc, literal_char_dec, union_to_inter)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "/.webm") (re.union (str.to_re "?") (str.to_re "\u{5c}") (str.to_re "/")) (str.to_re "/smiU\u{a}")) (re.comp (re.++ (str.to_re "/.webm") (re.inter(str.to_re ">") (str.to_re "\u{5c}") (str.to_re "0")) (str.to_re "/smiU\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "/.webm") (re.union (str.to_re "?") (str.to_re "\u{5c}") (str.to_re "/")) (str.to_re "/smiU\u{a}"))) (re.++ (str.to_re "/.webm") (re.inter(str.to_re ">") (str.to_re "\u{5c}") (str.to_re "0")) (str.to_re "/smiU\u{a}"))))))

(check-sat)
(exit)
