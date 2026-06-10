;; Equivalence-Preserving Mutation Benchmark
;; Base: xml_tag
;; Transforms: plus_to_cat_star, star_unroll, double_comp, inter_idemp, absorb_empty
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (str.to_re "<") (re.+ (re.union (re.range "a" "z") (re.range "A" "Z")))) (re.* (re.++ (re.++ (re.++ (re.++ (re.++ (str.to_re " ") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")))) (str.to_re "=")) (str.to_re "'")) (re.* (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re " ")))) (str.to_re "'")))) (str.to_re ">")) (re.* (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re " ")) (str.to_re ".")))) (str.to_re "</")) (re.+ (re.union (re.range "a" "z") (re.range "A" "Z")))) (str.to_re ">")) (re.union (re.++ (re.comp (re.comp (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (str.to_re "<") (re.+ (re.union (re.range "a" "z") (re.range "A" "Z")))) (re.* (re.++ (re.++ (re.++ (re.++ (re.++ (re.inter (str.to_re " ") (str.to_re " ")) (re.++ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (re.* (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))))) (str.to_re "=")) (str.to_re "'")) (re.* (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re " ")))) (str.to_re "'")))) (str.to_re ">")) (re.union (str.to_re "") (re.++ (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re " ")) (str.to_re ".")) (re.* (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re " ")) (str.to_re ".")))))) (str.to_re "</")) (re.+ (re.union (re.range "a" "z") (re.range "A" "Z")))))) (str.to_re ">")) re.none))))

(check-sat)
(exit)
