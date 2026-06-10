;; Equivalence-Preserving Mutation Benchmark
;; Base: uuid
;; Transforms: concat_assoc, union_assoc, double_comp, double_comp
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ ((_ re.loop 8 8) (re.union (re.union (re.range "0" "9") (re.range "a" "f")) (re.range "A" "F"))) (str.to_re "-")) ((_ re.loop 4 4) (re.union (re.union (re.range "0" "9") (re.range "a" "f")) (re.range "A" "F")))) (str.to_re "-")) ((_ re.loop 4 4) (re.union (re.union (re.range "0" "9") (re.range "a" "f")) (re.range "A" "F")))) (str.to_re "-")) ((_ re.loop 4 4) (re.union (re.union (re.range "0" "9") (re.range "a" "f")) (re.range "A" "F")))) (str.to_re "-")) ((_ re.loop 12 12) (re.union (re.union (re.range "0" "9") (re.range "a" "f")) (re.range "A" "F")))) (re.++ (re.++ (re.++ (re.comp (re.comp (re.++ (re.++ (re.comp (re.comp (re.++ (re.++ ((_ re.loop 8 8) (re.union (re.union (re.range "0" "9") (re.range "a" "f")) (re.range "A" "F"))) (str.to_re "-")) ((_ re.loop 4 4) (re.union (re.union (re.range "0" "9") (re.range "a" "f")) (re.range "A" "F")))))) (str.to_re "-")) ((_ re.loop 4 4) (re.union (re.union (re.range "0" "9") (re.range "a" "f")) (re.range "A" "F")))))) (str.to_re "-")) ((_ re.loop 4 4) (re.union (re.union (re.range "0" "9") (re.range "a" "f")) (re.range "A" "F")))) (re.++ (str.to_re "-") ((_ re.loop 12 12) (re.union (re.range "0" "9") (re.union (re.range "a" "f") (re.range "A" "F")))))))))

(check-sat)
(exit)
