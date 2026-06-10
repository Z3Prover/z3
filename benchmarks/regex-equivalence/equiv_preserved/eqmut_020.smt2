;; Equivalence-Preserving Mutation Benchmark
;; Base: phone_us
;; Transforms: concat_assoc, concat_assoc, double_comp, union_idemp
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.union (re.union (re.++ (re.++ (re.++ (re.++ (re.++ (str.to_re "(") ((_ re.loop 3 3) (re.range "0" "9"))) (str.to_re ") ")) ((_ re.loop 3 3) (re.range "0" "9"))) (str.to_re "-")) ((_ re.loop 4 4) (re.range "0" "9"))) (re.++ (re.++ (re.++ (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "-")) ((_ re.loop 3 3) (re.range "0" "9"))) (str.to_re "-")) ((_ re.loop 4 4) (re.range "0" "9")))) (re.++ (str.to_re "+1") ((_ re.loop 10 10) (re.range "0" "9")))) (re.union (re.union (re.++ (re.++ (re.++ (str.to_re "(") ((_ re.loop 3 3) (re.range "0" "9"))) (re.++ (str.to_re ") ") (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "-")))) ((_ re.loop 4 4) (re.union (re.range "0" "9") (re.range "0" "9")))) (re.++ (re.comp (re.comp (re.++ (re.++ (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "-")) ((_ re.loop 3 3) (re.range "0" "9"))) (str.to_re "-")))) ((_ re.loop 4 4) (re.range "0" "9")))) (re.++ (str.to_re "+1") ((_ re.loop 10 10) (re.range "0" "9")))))))

(check-sat)
(exit)
