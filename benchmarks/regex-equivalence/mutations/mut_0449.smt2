;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance15629.smt2
;; Mutations:  star_to_plus, intersect_max_len_20, range_shrink_lo
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
;; R2: mutated (star_to_plus, intersect_max_len_20, range_shrink_lo)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.opt (str.to_re "$")) (re.union (re.+ (re.range "0" "9")) (re.++ ((_ re.loop 1 3) (re.range "0" "9")) (re.* (re.++ (str.to_re ",") ((_ re.loop 3 3) (re.range "0" "9")))))) (re.opt (re.++ (str.to_re ".") ((_ re.loop 2 2) (re.range "0" "9")) (re.* (re.range "0" "9")))) (str.to_re "\u{a}")) (re.comp (re.++ (re.opt (str.to_re "$")) (re.union (re.+ (re.range "1" "9")) (re.inter (re.++ ((_ re.loop 1 3) (re.range "0" "9")) (re.* (re.++ (str.to_re ",") ((_ re.loop 3 3) (re.range "0" "9"))))) ((_ re.loop 0 20) re.allchar))) (re.opt (re.++ (str.to_re ".") ((_ re.loop 2 2) (re.range "0" "9")) (re.+ (re.range "0" "9")))) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.opt (str.to_re "$")) (re.union (re.+ (re.range "0" "9")) (re.++ ((_ re.loop 1 3) (re.range "0" "9")) (re.* (re.++ (str.to_re ",") ((_ re.loop 3 3) (re.range "0" "9")))))) (re.opt (re.++ (str.to_re ".") ((_ re.loop 2 2) (re.range "0" "9")) (re.* (re.range "0" "9")))) (str.to_re "\u{a}"))) (re.++ (re.opt (str.to_re "$")) (re.union (re.+ (re.range "1" "9")) (re.inter (re.++ ((_ re.loop 1 3) (re.range "0" "9")) (re.* (re.++ (str.to_re ",") ((_ re.loop 3 3) (re.range "0" "9"))))) ((_ re.loop 0 20) re.allchar))) (re.opt (re.++ (str.to_re ".") ((_ re.loop 2 2) (re.range "0" "9")) (re.+ (re.range "0" "9")))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
