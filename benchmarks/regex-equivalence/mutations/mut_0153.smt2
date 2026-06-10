;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance10482.smt2
;; Mutations:  literal_char_dec, range_shrink_hi, range_shrink_hi
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
;; R2: mutated (literal_char_dec, range_shrink_hi, range_shrink_hi)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.union (re.++ (str.to_re " ") (re.range "1" "9")) (re.range "1" "9") (re.++ (str.to_re "0") (re.range "1" "9")) (str.to_re "10") (str.to_re "11") (str.to_re "12")) (re.range "0" "5") (re.range "0" "9") (str.to_re "\u{a}")) (re.comp (re.++ (re.union (re.++ (str.to_re " ") (re.range "1" "9")) (re.range "1" "8") (re.++ (str.to_re "0") (re.range "1" "8")) (str.to_re "1/") (str.to_re "11") (str.to_re "12")) (re.range "0" "5") (re.range "0" "9") (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.union (re.++ (str.to_re " ") (re.range "1" "9")) (re.range "1" "9") (re.++ (str.to_re "0") (re.range "1" "9")) (str.to_re "10") (str.to_re "11") (str.to_re "12")) (re.range "0" "5") (re.range "0" "9") (str.to_re "\u{a}"))) (re.++ (re.union (re.++ (str.to_re " ") (re.range "1" "9")) (re.range "1" "8") (re.++ (str.to_re "0") (re.range "1" "8")) (str.to_re "1/") (str.to_re "11") (str.to_re "12")) (re.range "0" "5") (re.range "0" "9") (str.to_re "\u{a}"))))))

(check-sat)
(exit)
