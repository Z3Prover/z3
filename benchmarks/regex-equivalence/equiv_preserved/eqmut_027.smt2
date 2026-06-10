;; Equivalence-Preserving Mutation Benchmark
;; Base: css_color
;; Transforms: union_assoc, distrib_right, double_comp, double_comp
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ (str.to_re "#") (re.union ((_ re.loop 3 3) (re.union (re.union (re.range "0" "9") (re.range "a" "f")) (re.range "A" "F"))) ((_ re.loop 6 6) (re.union (re.union (re.range "0" "9") (re.range "a" "f")) (re.range "A" "F"))))) (re.union (re.++ (str.to_re "#") ((_ re.loop 3 3) (re.union (re.comp (re.comp (re.union (re.range "0" "9") (re.range "a" "f")))) (re.range "A" "F")))) (re.++ (re.comp (re.comp (str.to_re "#"))) ((_ re.loop 6 6) (re.union (re.range "0" "9") (re.union (re.range "a" "f") (re.range "A" "F")))))))))

(check-sat)
(exit)
