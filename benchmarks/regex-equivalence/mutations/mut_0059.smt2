;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance01354.smt2
;; Mutations:  intersect_min_len_5, literal_char_inc, intersect_max_len_10
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
;; R2: mutated (intersect_min_len_5, literal_char_inc, intersect_max_len_10)
(assert
  (str.in_re x
    (re.union (re.inter (re.union (re.++ (re.opt (str.to_re "-")) (str.to_re "1000") (re.opt (re.++ (str.to_re ".") ((_ re.loop 1 3) (str.to_re "0"))))) (re.++ (re.opt (str.to_re "-")) ((_ re.loop 1 3) (re.range "0" "9"))) (re.++ (re.opt (str.to_re "-")) ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 1 3) (re.range "0" "9"))) (re.++ (re.opt (str.to_re "-")) (str.to_re "\u{a}.") ((_ re.loop 1 3) (re.range "0" "9")))) (re.comp (re.union (re.++ (re.inter (re.opt (str.to_re "-")) ((_ re.loop 0 10) re.allchar)) (str.to_re "1000") (re.opt (re.++ (str.to_re ".") ((_ re.loop 1 3) (str.to_re "1"))))) (re.++ (re.opt (str.to_re "-")) ((_ re.loop 1 3) (re.range "0" "9"))) (re.inter (re.++ (re.opt (str.to_re "-")) ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 1 3) (re.range "0" "9"))) (re.++ ((_ re.loop 5 5) re.allchar) re.all)) (re.++ (re.opt (str.to_re "-")) (str.to_re "\u{a}.") ((_ re.loop 1 3) (re.range "0" "9")))))) (re.inter (re.comp (re.union (re.++ (re.opt (str.to_re "-")) (str.to_re "1000") (re.opt (re.++ (str.to_re ".") ((_ re.loop 1 3) (str.to_re "0"))))) (re.++ (re.opt (str.to_re "-")) ((_ re.loop 1 3) (re.range "0" "9"))) (re.++ (re.opt (str.to_re "-")) ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 1 3) (re.range "0" "9"))) (re.++ (re.opt (str.to_re "-")) (str.to_re "\u{a}.") ((_ re.loop 1 3) (re.range "0" "9"))))) (re.union (re.++ (re.inter (re.opt (str.to_re "-")) ((_ re.loop 0 10) re.allchar)) (str.to_re "1000") (re.opt (re.++ (str.to_re ".") ((_ re.loop 1 3) (str.to_re "1"))))) (re.++ (re.opt (str.to_re "-")) ((_ re.loop 1 3) (re.range "0" "9"))) (re.inter (re.++ (re.opt (str.to_re "-")) ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 1 3) (re.range "0" "9"))) (re.++ ((_ re.loop 5 5) re.allchar) re.all)) (re.++ (re.opt (str.to_re "-")) (str.to_re "\u{a}.") ((_ re.loop 1 3) (re.range "0" "9"))))))))

(check-sat)
(exit)
