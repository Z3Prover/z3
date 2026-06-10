;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance12677.smt2
;; Mutations:  range_shrink_hi, range_shrink_hi, plus_to_star
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_hi, range_shrink_hi, plus_to_star)
(assert
  (not
    (=
      (re.union (re.++ (re.opt (re.++ (str.to_re ".") (re.+ (re.range "0" "9")))) ((_ re.loop 1 1) (re.range "1" "9")) (re.opt (re.+ (re.range "0" "9")))) (re.++ (str.to_re "\u{a}0.") (re.opt (re.+ (re.range "0" "9"))) ((_ re.loop 1 1) (re.range "1" "9")) (re.opt (re.+ (re.range "0" "9")))))
      (re.union (re.++ (re.opt (re.++ (str.to_re ".") (re.* (re.range "0" "9")))) ((_ re.loop 1 1) (re.range "1" "9")) (re.opt (re.+ (re.range "0" "8")))) (re.++ (str.to_re "\u{a}0.") (re.opt (re.+ (re.range "0" "9"))) ((_ re.loop 1 1) (re.range "1" "9")) (re.opt (re.+ (re.range "0" "8"))))))))

(check-sat)
(exit)
