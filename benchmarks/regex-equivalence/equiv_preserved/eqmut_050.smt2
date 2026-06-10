;; Equivalence-Preserving Mutation Benchmark
;; Base: log_timestamp
;; Transforms: concat_assoc, concat_assoc
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (str.to_re "[") ((_ re.loop 4 4) (re.range "0" "9"))) (str.to_re "-")) ((_ re.loop 2 2) (re.range "0" "9"))) (str.to_re "-")) ((_ re.loop 2 2) (re.range "0" "9"))) (str.to_re " ")) ((_ re.loop 2 2) (re.range "0" "9"))) (str.to_re ":")) ((_ re.loop 2 2) (re.range "0" "9"))) (str.to_re ":")) ((_ re.loop 2 2) (re.range "0" "9"))) (str.to_re "]")) (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (str.to_re "[") ((_ re.loop 4 4) (re.range "0" "9"))) (str.to_re "-")) ((_ re.loop 2 2) (re.range "0" "9"))) (str.to_re "-")) ((_ re.loop 2 2) (re.range "0" "9"))) (str.to_re " ")) ((_ re.loop 2 2) (re.range "0" "9"))) (str.to_re ":")) (re.++ ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re ":"))) (re.++ ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "]"))))))

(check-sat)
(exit)
