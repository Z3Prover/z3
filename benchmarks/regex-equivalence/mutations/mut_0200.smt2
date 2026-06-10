;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance02870.smt2
;; Mutations:  star_to_plus, literal_char_dec
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
;; R2: mutated (star_to_plus, literal_char_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "/filename=") (re.* (re.comp (str.to_re "\u{a}"))) (str.to_re ".rmf/i\u{a}")) (re.comp (re.++ (str.to_re "/filename<") (re.+ (re.comp (str.to_re "\u{a}"))) (str.to_re ".rmf/i\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "/filename=") (re.* (re.comp (str.to_re "\u{a}"))) (str.to_re ".rmf/i\u{a}"))) (re.++ (str.to_re "/filename<") (re.+ (re.comp (str.to_re "\u{a}"))) (str.to_re ".rmf/i\u{a}"))))))

(check-sat)
(exit)
