;; Equivalence-Preserving Mutation Benchmark
;; Base: ipv4_strict
;; Transforms: concat_assoc, concat_assoc
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ".")) ((_ re.loop 1 3) (re.range "0" "9"))) (str.to_re ".")) ((_ re.loop 1 3) (re.range "0" "9"))) (str.to_re ".")) ((_ re.loop 1 3) (re.range "0" "9"))) (re.++ (re.++ (re.++ (re.++ ((_ re.loop 1 3) (re.range "0" "9")) (re.++ (str.to_re ".") ((_ re.loop 1 3) (re.range "0" "9")))) (str.to_re ".")) ((_ re.loop 1 3) (re.range "0" "9"))) (re.++ (str.to_re ".") ((_ re.loop 1 3) (re.range "0" "9")))))))

(check-sat)
(exit)
