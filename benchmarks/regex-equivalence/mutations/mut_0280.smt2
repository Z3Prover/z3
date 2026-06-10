;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance06106.smt2
;; Mutations:  range_shrink_lo, bound_lower_dec
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
;; R2: mutated (range_shrink_lo, bound_lower_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.union (str.to_re "t") (str.to_re "T")) (re.union (str.to_re "o") (str.to_re "O")) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) ((_ re.loop 4 4) (re.range "0" "9")) (re.comp (re.range "0" "9")) (str.to_re "\u{a}")) (re.comp (re.++ (re.union (str.to_re "t") (str.to_re "T")) (re.union (str.to_re "o") (str.to_re "O")) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) ((_ re.loop 3 4) (re.range "1" "9")) (re.comp (re.range "0" "9")) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.union (str.to_re "t") (str.to_re "T")) (re.union (str.to_re "o") (str.to_re "O")) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) ((_ re.loop 4 4) (re.range "0" "9")) (re.comp (re.range "0" "9")) (str.to_re "\u{a}"))) (re.++ (re.union (str.to_re "t") (str.to_re "T")) (re.union (str.to_re "o") (str.to_re "O")) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) ((_ re.loop 3 4) (re.range "1" "9")) (re.comp (re.range "0" "9")) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
