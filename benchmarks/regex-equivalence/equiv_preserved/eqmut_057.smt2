;; Equivalence-Preserving Mutation Benchmark
;; Base: semver
;; Transforms: union_assoc, concat_assoc, union_idemp, double_comp, concat_eps
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.+ (re.range "0" "9")) (str.to_re ".")) (re.+ (re.range "0" "9"))) (str.to_re ".")) (re.+ (re.range "0" "9"))) (re.opt (re.++ (str.to_re "-") (re.+ (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re ".")))))) (re.opt (re.++ (str.to_re "+") (re.+ (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re ".")))))) (re.++ (re.++ (re.++ (re.union (re.++ (re.++ (re.+ (re.range "0" "9")) (str.to_re ".")) (re.+ (re.range "0" "9"))) (re.++ (re.++ (re.+ (re.range "0" "9")) (str.to_re ".")) (re.+ (re.range "0" "9")))) (re.++ (str.to_re ".") (re.+ (re.range "0" "9")))) (re.opt (re.++ (str.to_re "-") (re.+ (re.union (re.union (re.range "a" "z") (re.union (re.++ (re.range "A" "Z") (str.to_re "")) (re.range "0" "9"))) (str.to_re ".")))))) (re.opt (re.++ (str.to_re "+") (re.+ (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (re.comp (re.comp (str.to_re ".")))))))))))

(check-sat)
(exit)
