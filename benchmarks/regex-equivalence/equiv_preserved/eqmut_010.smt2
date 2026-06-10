;; Equivalence-Preserving Mutation Benchmark
;; Base: url_full
;; Transforms: star_idemp, concat_assoc, double_comp, double_comp, concat_eps
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ (re.++ (re.++ (re.++ (re.++ (str.to_re "http") (re.opt (str.to_re "s"))) (str.to_re "://")) (re.+ (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "-")) (str.to_re ".")))) (re.opt (re.++ (str.to_re ":") (re.+ (re.range "0" "9"))))) (re.* (re.++ (str.to_re "/") (re.* (re.union (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "-")) (str.to_re "_")) (str.to_re ".")))))) (re.comp (re.comp (re.++ (re.++ (re.comp (re.++ (re.comp (re.++ (re.++ (str.to_re "http") (re.opt (str.to_re "s"))) (str.to_re "://"))) (str.to_re ""))) (re.+ (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "-")) (str.to_re ".")))) (re.++ (re.opt (re.++ (str.to_re ":") (re.+ (re.range "0" "9")))) (re.* (re.* (re.++ (str.to_re "/") (re.* (re.union (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "-")) (str.to_re "_")) (str.to_re ".")))))))))))))

(check-sat)
(exit)
