;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00391.smt2
;; Mutations:  intersect_no_alnum3, intersect_no_upper2
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
;; R2: mutated (intersect_no_alnum3, intersect_no_upper2)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.+ (re.union (re.range "0" "9") (str.to_re ",") (str.to_re "+") (str.to_re "(") (str.to_re ")") (str.to_re " "))) (re.* (re.++ (str.to_re ",") (re.+ (re.range "0" "9")))) (str.to_re "\u{a}")) (re.comp (re.++ (re.inter (re.+ (re.union (re.range "0" "9") (str.to_re ",") (str.to_re "+") (str.to_re "(") (str.to_re ")") (str.to_re " "))) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) (re.inter (re.* (re.++ (str.to_re ",") (re.+ (re.range "0" "9")))) (re.comp (re.++ re.all ((_ re.loop 3 3) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) re.all))) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.+ (re.union (re.range "0" "9") (str.to_re ",") (str.to_re "+") (str.to_re "(") (str.to_re ")") (str.to_re " "))) (re.* (re.++ (str.to_re ",") (re.+ (re.range "0" "9")))) (str.to_re "\u{a}"))) (re.++ (re.inter (re.+ (re.union (re.range "0" "9") (str.to_re ",") (str.to_re "+") (str.to_re "(") (str.to_re ")") (str.to_re " "))) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) (re.inter (re.* (re.++ (str.to_re ",") (re.+ (re.range "0" "9")))) (re.comp (re.++ re.all ((_ re.loop 3 3) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) re.all))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
