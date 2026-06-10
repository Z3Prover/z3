;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11815.smt2
;; Mutations:  literal_char_inc, literal_char_dec, literal_char_dec
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
;; R2: mutated (literal_char_inc, literal_char_dec, literal_char_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.union (str.to_re "A") (str.to_re "a") (str.to_re "E") (str.to_re "e") (str.to_re "I") (str.to_re "i") (str.to_re "O") (str.to_re "o") (str.to_re "U") (str.to_re "u") (str.to_re "Y") (str.to_re "y")) (str.to_re "\u{a}")) (re.comp (re.++ (re.union (str.to_re "A") (str.to_re "a") (str.to_re "E") (str.to_re "e") (str.to_re "I") (str.to_re "i") (str.to_re "N") (str.to_re "o") (str.to_re "U") (str.to_re "t") (str.to_re "Y") (str.to_re "z")) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.union (str.to_re "A") (str.to_re "a") (str.to_re "E") (str.to_re "e") (str.to_re "I") (str.to_re "i") (str.to_re "O") (str.to_re "o") (str.to_re "U") (str.to_re "u") (str.to_re "Y") (str.to_re "y")) (str.to_re "\u{a}"))) (re.++ (re.union (str.to_re "A") (str.to_re "a") (str.to_re "E") (str.to_re "e") (str.to_re "I") (str.to_re "i") (str.to_re "N") (str.to_re "o") (str.to_re "U") (str.to_re "t") (str.to_re "Y") (str.to_re "z")) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
