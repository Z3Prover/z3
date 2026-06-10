;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance12385.smt2
;; Mutations:  union_to_inter, literal_char_dec, bound_upper_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (union_to_inter, literal_char_dec, bound_upper_inc)
(assert
  (not
    (=
      (re.++ (re.opt (re.union (re.++ (re.union (str.to_re "0") (str.to_re "1")) (re.union (str.to_re ".") (str.to_re "-") (str.to_re " ") (str.to_re "+")) (str.to_re "(") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ")") (re.opt (re.union (str.to_re ".") (str.to_re "-") (str.to_re " ") (str.to_re "+")))) (re.++ (re.union (str.to_re "0") (str.to_re "1")) (re.union (str.to_re ".") (str.to_re "-") (str.to_re " ") (str.to_re "+")) ((_ re.loop 3 3) (re.range "0" "9")) (re.union (str.to_re ".") (str.to_re "-") (str.to_re " ") (str.to_re "+"))) (re.++ (str.to_re "(") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ")") (re.opt (str.to_re " "))) (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (re.union (str.to_re "-") (str.to_re " ") (str.to_re "."))))) ((_ re.loop 3 3) (re.range "0" "9")) (re.union (str.to_re "-") (str.to_re " ") (str.to_re ".")) ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "\u{a}"))
      (re.++ (re.opt (re.union (re.++ (re.union (str.to_re "0") (str.to_re "1")) (re.union (str.to_re ".") (str.to_re "-") (str.to_re " ") (str.to_re "+")) (str.to_re "(") ((_ re.loop 3 4) (re.range "0" "9")) (str.to_re ")") (re.opt (re.union (str.to_re ".") (str.to_re "-") (str.to_re " ") (str.to_re "+")))) (re.++ (re.union (str.to_re "/") (str.to_re "1")) (re.union (str.to_re ".") (str.to_re "-") (str.to_re " ") (str.to_re "+")) ((_ re.loop 3 3) (re.range "0" "9")) (re.union (str.to_re ".") (str.to_re "-") (str.to_re " ") (str.to_re "+"))) (re.++ (str.to_re "(") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ")") (re.opt (str.to_re " "))) (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (re.inter (str.to_re "-") (str.to_re " ") (str.to_re "."))))) ((_ re.loop 3 3) (re.range "0" "9")) (re.union (str.to_re "-") (str.to_re " ") (str.to_re ".")) ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "\u{a}")))))

(check-sat)
(exit)
