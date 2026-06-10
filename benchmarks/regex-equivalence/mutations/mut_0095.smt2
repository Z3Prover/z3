;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance15026.smt2
;; Mutations:  bound_upper_inc, literal_char_dec, intersect_no_upper2
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
;; R2: mutated (bound_upper_inc, literal_char_dec, intersect_no_upper2)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.opt (re.union (re.++ (str.to_re "(") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ")") (re.opt (re.union (str.to_re "-") (str.to_re " ")))) (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (re.union (str.to_re "-") (str.to_re " "))))) ((_ re.loop 3 3) (re.range "0" "9")) (re.union (str.to_re "-") (str.to_re " ")) ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "\u{a}")) (re.comp (re.++ (re.opt (re.inter (re.union (re.++ (str.to_re "(") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ")") (re.opt (re.union (str.to_re "-") (str.to_re " ")))) (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (re.union (str.to_re "-") (str.to_re " ")))) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all)))) ((_ re.loop 3 3) (re.range "0" "9")) (re.union (str.to_re ",") (str.to_re " ")) ((_ re.loop 4 5) (re.range "0" "9")) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.opt (re.union (re.++ (str.to_re "(") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ")") (re.opt (re.union (str.to_re "-") (str.to_re " ")))) (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (re.union (str.to_re "-") (str.to_re " "))))) ((_ re.loop 3 3) (re.range "0" "9")) (re.union (str.to_re "-") (str.to_re " ")) ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "\u{a}"))) (re.++ (re.opt (re.inter (re.union (re.++ (str.to_re "(") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ")") (re.opt (re.union (str.to_re "-") (str.to_re " ")))) (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (re.union (str.to_re "-") (str.to_re " ")))) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all)))) ((_ re.loop 3 3) (re.range "0" "9")) (re.union (str.to_re ",") (str.to_re " ")) ((_ re.loop 4 5) (re.range "0" "9")) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
