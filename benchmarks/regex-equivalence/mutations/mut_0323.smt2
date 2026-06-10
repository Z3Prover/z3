;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance04028.smt2
;; Mutations:  literal_char_dec, literal_char_dec
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
;; R2: mutated (literal_char_dec, literal_char_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.* (re.union (str.to_re "o") (str.to_re "O") (str.to_re "0"))) (re.union (str.to_re "|") (str.to_re ":") (str.to_re ";") (str.to_re "=") (str.to_re "X") (str.to_re "^")) (re.* (re.union (str.to_re "-") (str.to_re "'"))) (re.union (str.to_re ")") (str.to_re "(") (str.to_re "o") (str.to_re "O") (str.to_re "0") (str.to_re "]") (str.to_re "[") (str.to_re "D") (str.to_re "P") (str.to_re "p") (str.to_re "*") (str.to_re ">") (str.to_re "X") (str.to_re "^") (str.to_re "@")) (str.to_re "\u{a}")) (re.comp (re.++ (re.* (re.union (str.to_re "o") (str.to_re "O") (str.to_re "0"))) (re.union (str.to_re "|") (str.to_re ":") (str.to_re ";") (str.to_re "=") (str.to_re "X") (str.to_re "^")) (re.* (re.union (str.to_re ",") (str.to_re "'"))) (re.union (str.to_re ")") (str.to_re "(") (str.to_re "o") (str.to_re "N") (str.to_re "0") (str.to_re "]") (str.to_re "[") (str.to_re "D") (str.to_re "P") (str.to_re "p") (str.to_re "*") (str.to_re ">") (str.to_re "X") (str.to_re "^") (str.to_re "@")) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.* (re.union (str.to_re "o") (str.to_re "O") (str.to_re "0"))) (re.union (str.to_re "|") (str.to_re ":") (str.to_re ";") (str.to_re "=") (str.to_re "X") (str.to_re "^")) (re.* (re.union (str.to_re "-") (str.to_re "'"))) (re.union (str.to_re ")") (str.to_re "(") (str.to_re "o") (str.to_re "O") (str.to_re "0") (str.to_re "]") (str.to_re "[") (str.to_re "D") (str.to_re "P") (str.to_re "p") (str.to_re "*") (str.to_re ">") (str.to_re "X") (str.to_re "^") (str.to_re "@")) (str.to_re "\u{a}"))) (re.++ (re.* (re.union (str.to_re "o") (str.to_re "O") (str.to_re "0"))) (re.union (str.to_re "|") (str.to_re ":") (str.to_re ";") (str.to_re "=") (str.to_re "X") (str.to_re "^")) (re.* (re.union (str.to_re ",") (str.to_re "'"))) (re.union (str.to_re ")") (str.to_re "(") (str.to_re "o") (str.to_re "N") (str.to_re "0") (str.to_re "]") (str.to_re "[") (str.to_re "D") (str.to_re "P") (str.to_re "p") (str.to_re "*") (str.to_re ">") (str.to_re "X") (str.to_re "^") (str.to_re "@")) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
