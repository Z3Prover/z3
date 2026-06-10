;; Equivalence-Preserving Mutation Benchmark
;; Base: path_traversal
;; Transforms: star_idemp, concat_assoc
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.inter (re.++ (re.++ (re.* re.allchar) (str.to_re "../")) (re.* re.allchar)) (re.comp (re.++ (re.++ (re.* re.allchar) (str.to_re "/etc/passwd")) (re.* re.allchar)))) (re.inter (re.++ (re.++ (re.* re.allchar) (str.to_re "../")) (re.* re.allchar)) (re.comp (re.++ (re.* (re.* re.allchar)) (re.++ (str.to_re "/etc/passwd") (re.* re.allchar))))))))

(check-sat)
(exit)
