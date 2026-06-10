;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance09875.smt2
;; Mutations:  range_expand_hi, range_shrink_hi
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)

(declare-const x String)

;; R1: original
;; R2: mutated (range_expand_hi, range_shrink_hi)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.+ (re.union (re.range "a" "z") (re.range "A" "Z"))) (re.opt (re.++ (re.union (str.to_re "-") (str.to_re "'") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.+ (re.union (re.range "a" "z") (re.range "A" "Z"))))) (str.to_re "\u{a}")) (re.comp (re.++ (re.+ (re.union (re.range "a" "z") (re.range "A" "Y"))) (re.opt (re.++ (re.union (str.to_re "-") (str.to_re "'") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.+ (re.union (re.range "a" "z") (re.range "A" "["))))) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.+ (re.union (re.range "a" "z") (re.range "A" "Z"))) (re.opt (re.++ (re.union (str.to_re "-") (str.to_re "'") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.+ (re.union (re.range "a" "z") (re.range "A" "Z"))))) (str.to_re "\u{a}"))) (re.++ (re.+ (re.union (re.range "a" "z") (re.range "A" "Y"))) (re.opt (re.++ (re.union (str.to_re "-") (str.to_re "'") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.+ (re.union (re.range "a" "z") (re.range "A" "["))))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
