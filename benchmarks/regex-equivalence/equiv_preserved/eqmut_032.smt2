;; Equivalence-Preserving Mutation Benchmark
;; Base: password_policy
;; Transforms: union_assoc, star_idemp
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.inter (re.inter (re.inter ((_ re.loop 8 64) (re.union (re.union (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "!")) (str.to_re "@")) (str.to_re "#")) (str.to_re "$"))) (re.++ (re.++ (re.* re.allchar) (re.range "0" "9")) (re.* re.allchar))) (re.++ (re.++ (re.* re.allchar) (re.range "A" "Z")) (re.* re.allchar))) (re.++ (re.++ (re.* re.allchar) (re.range "a" "z")) (re.* re.allchar))) (re.inter (re.inter (re.inter ((_ re.loop 8 64) (re.union (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "!")) (str.to_re "@")) (re.union (str.to_re "#") (str.to_re "$")))) (re.++ (re.++ (re.* re.allchar) (re.range "0" "9")) (re.* re.allchar))) (re.++ (re.++ (re.* re.allchar) (re.range "A" "Z")) (re.* re.allchar))) (re.++ (re.++ (re.* (re.* re.allchar)) (re.range "a" "z")) (re.* re.allchar))))))

(check-sat)
(exit)
