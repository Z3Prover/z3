;; Equivalence-Preserving Mutation Benchmark
;; Base: date_iso
;; Transforms: distrib_right, distrib_right, double_comp, union_idemp
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ (re.++ (re.++ (re.++ ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "-")) (re.union (re.++ (str.to_re "0") (re.range "1" "9")) (re.++ (str.to_re "1") (re.range "0" "2")))) (str.to_re "-")) (re.union (re.union (re.++ (str.to_re "0") (re.range "1" "9")) (re.++ (re.union (str.to_re "1") (str.to_re "2")) (re.range "0" "9"))) (re.++ (str.to_re "3") (re.union (str.to_re "0") (str.to_re "1"))))) (re.comp (re.comp (re.union (re.++ (re.++ (re.union (re.++ (re.++ ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "-")) (re.++ (str.to_re "0") (re.range "1" "9"))) (re.++ (re.++ ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "-")) (re.union (re.++ (str.to_re "1") (re.range "0" "2")) (re.++ (str.to_re "1") (re.range "0" "2"))))) (str.to_re "-")) (re.union (re.++ (str.to_re "0") (re.range "1" "9")) (re.++ (re.union (str.to_re "1") (str.to_re "2")) (re.range "0" "9")))) (re.++ (re.++ (re.union (re.++ (re.++ ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "-")) (re.++ (str.to_re "0") (re.range "1" "9"))) (re.++ (re.++ ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "-")) (re.++ (str.to_re "1") (re.range "0" "2")))) (str.to_re "-")) (re.++ (str.to_re "3") (re.union (str.to_re "0") (str.to_re "1"))))))))))

(check-sat)
(exit)
