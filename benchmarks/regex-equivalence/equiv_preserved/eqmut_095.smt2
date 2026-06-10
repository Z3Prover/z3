;; Equivalence-Preserving Mutation Benchmark
;; Base: nested_loops_comp
;; Transforms: star_idemp, star_unroll, union_idemp
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.inter (re.++ ((_ re.loop 2 5) (re.union (str.to_re "a") (str.to_re "b"))) (re.* (str.to_re "c"))) (re.comp (re.++ ((_ re.loop 3 3) (str.to_re "a")) (re.* re.allchar)))) (re.inter (re.++ ((_ re.loop 2 5) (re.union (str.to_re "a") (str.to_re "b"))) (re.* (str.to_re "c"))) (re.comp (re.++ ((_ re.loop 3 3) (str.to_re "a")) (re.* (re.union (str.to_re "") (re.++ re.allchar (re.union (re.* re.allchar) (re.* re.allchar)))))))))))

(check-sat)
(exit)
