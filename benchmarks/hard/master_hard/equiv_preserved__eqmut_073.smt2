;; Equivalence-Preserving Mutation Benchmark
;; Base: sqli_pattern
;; Transforms: star_idemp, concat_assoc, double_comp, inter_idemp
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.inter (re.++ (re.++ (re.* re.allchar) (re.union (str.to_re "' OR ") (str.to_re "' AND "))) (re.* re.allchar)) (re.++ (re.++ (re.* re.allchar) (re.union (str.to_re "1=1") (str.to_re "'='"))) (re.* re.allchar))) (re.comp (re.comp (re.inter (re.++ (re.* re.allchar) (re.++ (re.union (str.to_re "' OR ") (str.to_re "' AND ")) (re.* re.allchar))) (re.++ (re.++ (re.* (re.* re.allchar)) (re.inter (re.union (str.to_re "1=1") (str.to_re "'='")) (re.union (str.to_re "1=1") (str.to_re "'='")))) (re.* re.allchar))))))))

(check-sat)
(exit)
