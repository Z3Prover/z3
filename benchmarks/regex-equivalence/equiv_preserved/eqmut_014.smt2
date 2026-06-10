;; Equivalence-Preserving Mutation Benchmark
;; Base: url_full
;; Transforms: union_assoc, union_assoc, union_idemp, inter_idemp
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ (re.++ (re.++ (re.++ (re.++ (str.to_re "http") (re.opt (str.to_re "s"))) (str.to_re "://")) (re.+ (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "-")) (str.to_re ".")))) (re.opt (re.++ (str.to_re ":") (re.+ (re.range "0" "9"))))) (re.* (re.++ (str.to_re "/") (re.* (re.union (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "-")) (str.to_re "_")) (str.to_re ".")))))) (re.++ (re.++ (re.++ (re.++ (re.++ (str.to_re "http") (re.opt (str.to_re "s"))) (str.to_re "://")) (re.+ (re.union (re.union (re.range "a" "z") (re.inter (re.range "A" "Z") (re.range "A" "Z"))) (re.union (re.union (re.range "0" "9") (str.to_re "-")) (str.to_re "."))))) (re.opt (re.++ (str.to_re ":") (re.+ (re.union (re.range "0" "9") (re.range "0" "9")))))) (re.* (re.++ (str.to_re "/") (re.* (re.union (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "-")) (str.to_re "_")) (str.to_re ".")))))))))

(check-sat)
(exit)
