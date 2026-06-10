;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11767.smt2
;; Mutations:  bound_lower_dec, union_to_inter, range_shrink_lo
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
;; R2: mutated (bound_lower_dec, union_to_inter, range_shrink_lo)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ ((_ re.loop 3 3) (re.range "1" "9")) (re.opt (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "\u{a}")) (re.comp (re.++ ((_ re.loop 3 3) (re.range "2" "9")) (re.opt (re.inter(str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) ((_ re.loop 2 3) (re.range "0" "9")) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ ((_ re.loop 3 3) (re.range "1" "9")) (re.opt (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "\u{a}"))) (re.++ ((_ re.loop 3 3) (re.range "2" "9")) (re.opt (re.inter(str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) ((_ re.loop 2 3) (re.range "0" "9")) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
