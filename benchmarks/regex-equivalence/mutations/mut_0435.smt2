;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00724.smt2
;; Mutations:  literal_char_inc, literal_char_dec, range_shrink_lo
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
;; R2: mutated (literal_char_inc, literal_char_dec, range_shrink_lo)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "\u{a}") (re.range "0" "9") (str.to_re "1") (re.union (str.to_re "0") (str.to_re "1") (str.to_re "2") (str.to_re "3") (str.to_re "4") (str.to_re "5") (str.to_re "6") (str.to_re "7") (str.to_re "8") (str.to_re "9"))) (re.comp (re.++ (str.to_re "\u{a}") (re.range "1" "9") (str.to_re "1") (re.union (str.to_re "0") (str.to_re "1") (str.to_re "1") (str.to_re "3") (str.to_re "4") (str.to_re "5") (str.to_re "6") (str.to_re "7") (str.to_re "9") (str.to_re "9"))))) (re.inter (re.comp (re.++ (str.to_re "\u{a}") (re.range "0" "9") (str.to_re "1") (re.union (str.to_re "0") (str.to_re "1") (str.to_re "2") (str.to_re "3") (str.to_re "4") (str.to_re "5") (str.to_re "6") (str.to_re "7") (str.to_re "8") (str.to_re "9")))) (re.++ (str.to_re "\u{a}") (re.range "1" "9") (str.to_re "1") (re.union (str.to_re "0") (str.to_re "1") (str.to_re "1") (str.to_re "3") (str.to_re "4") (str.to_re "5") (str.to_re "6") (str.to_re "7") (str.to_re "9") (str.to_re "9")))))))

(check-sat)
(exit)
