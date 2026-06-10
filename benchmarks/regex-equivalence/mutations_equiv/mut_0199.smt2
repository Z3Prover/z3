;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance14786.smt2
;; Mutations:  union_to_inter, intersect_no_digits4, union_to_inter
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (union_to_inter, intersect_no_digits4, union_to_inter)
(assert
  (not
    (=
      (re.union (re.++ (str.to_re "/*") (re.* (re.union (re.range "0" "9") (re.comp (re.range "0" "9")))) (str.to_re "*/")) (re.++ (str.to_re "/*") (re.* (re.union (re.* (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.* re.allchar))) (str.to_re "*/")) (re.++ (str.to_re "//") (re.* re.allchar)) (re.++ (str.to_re "/") (re.* (str.to_re "\u{5c}")) (re.* (re.union (str.to_re "\u{5c}") (str.to_re "d") (str.to_re "D"))) (re.* (str.to_re "\u{5c}")) (str.to_re "/")) (re.++ (re.+ (re.++ (re.* (re.union (str.to_re "\u{d}") (str.to_re "\u{a}") (str.to_re " "))) (str.to_re "//") (re.* (re.union (str.to_re "\u{d}") (str.to_re "\u{a}"))))) (str.to_re "\u{a}")))
      (re.union (re.++ (str.to_re "/*") (re.* (re.union (re.range "0" "9") (re.comp (re.range "0" "9")))) (str.to_re "*/")) (re.++ (str.to_re "/*") (re.* (re.inter (re.* (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.* re.allchar))) (str.to_re "*/")) (re.++ (str.to_re "//") (re.* re.allchar)) (re.++ (str.to_re "/") (re.* (re.inter (str.to_re "\u{5c}") (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all)))) (re.* (re.union (str.to_re "\u{5c}") (str.to_re "d") (str.to_re "D"))) (re.* (str.to_re "\u{5c}")) (str.to_re "/")) (re.++ (re.+ (re.++ (re.* (re.inter (str.to_re "\u{d}") (str.to_re "\u{a}") (str.to_re " "))) (str.to_re "//") (re.* (re.union (str.to_re "\u{d}") (str.to_re "\u{a}"))))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
