;; Equivalence-Preserving Mutation Benchmark
;; Base: boolean_complex
;; Transforms: demorgan_union, concat_assoc, double_comp
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.inter (re.comp (re.union (re.++ (re.++ (re.* (str.to_re "a")) (str.to_re "b")) (re.* (str.to_re "c"))) (re.++ (re.++ (re.* (str.to_re "d")) (str.to_re "e")) (re.* (str.to_re "f"))))) (re.union (re.++ (re.+ (str.to_re "x")) (re.* (str.to_re "y"))) (re.comp (re.++ (re.* (str.to_re "z")) (re.+ (str.to_re "w")))))) (re.inter (re.inter (re.comp (re.++ (re.++ (re.* (str.to_re "a")) (str.to_re "b")) (re.* (str.to_re "c")))) (re.comp (re.++ (re.* (str.to_re "d")) (re.comp (re.comp (re.++ (str.to_re "e") (re.* (str.to_re "f")))))))) (re.union (re.++ (re.+ (str.to_re "x")) (re.* (str.to_re "y"))) (re.comp (re.++ (re.* (str.to_re "z")) (re.+ (str.to_re "w")))))))))

(check-sat)
(exit)
