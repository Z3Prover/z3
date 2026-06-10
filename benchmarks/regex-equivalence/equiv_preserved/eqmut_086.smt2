;; Equivalence-Preserving Mutation Benchmark
;; Base: base64
;; Transforms: plus_to_cat_star, concat_assoc, union_idemp, double_comp
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ (re.+ (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "+")) (str.to_re "/"))) (re.opt (re.union (str.to_re "==") (str.to_re "=")))) (re.comp (re.comp (re.++ (re.union (re.union (re.union (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "A" "Z"))) (re.range "0" "9")) (str.to_re "+")) (str.to_re "/")) (re.++ (re.* (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "+")) (str.to_re "/"))) (re.opt (re.union (str.to_re "==") (str.to_re "="))))))))))

(check-sat)
(exit)
