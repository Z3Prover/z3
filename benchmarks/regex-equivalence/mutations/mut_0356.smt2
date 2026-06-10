;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance08441.smt2
;; Mutations:  intersect_no_spaces, literal_char_dec, intersect_no_dot_dot
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
;; R2: mutated (intersect_no_spaces, literal_char_dec, intersect_no_dot_dot)
(assert
  (str.in_re x
    (re.union (re.inter (re.union (re.++ (str.to_re "protected") (re.* re.allchar) (str.to_re "public")) (re.++ (str.to_re "private") (re.* re.allchar) (str.to_re "protected")) (re.++ (str.to_re "\u{a}private") (re.* re.allchar) (str.to_re "public"))) (re.comp (re.union (re.++ (re.inter (str.to_re "protected") (re.comp (re.++ re.all (str.to_re "..") re.all))) (re.* re.allchar) (str.to_re "publib")) (re.++ (str.to_re "private") (re.* re.allchar) (str.to_re "protected")) (re.++ (re.inter (str.to_re "\u{a}private") (re.comp (re.++ re.all (str.to_re " ") re.all))) (re.* re.allchar) (str.to_re "public"))))) (re.inter (re.comp (re.union (re.++ (str.to_re "protected") (re.* re.allchar) (str.to_re "public")) (re.++ (str.to_re "private") (re.* re.allchar) (str.to_re "protected")) (re.++ (str.to_re "\u{a}private") (re.* re.allchar) (str.to_re "public")))) (re.union (re.++ (re.inter (str.to_re "protected") (re.comp (re.++ re.all (str.to_re "..") re.all))) (re.* re.allchar) (str.to_re "publib")) (re.++ (str.to_re "private") (re.* re.allchar) (str.to_re "protected")) (re.++ (re.inter (str.to_re "\u{a}private") (re.comp (re.++ re.all (str.to_re " ") re.all))) (re.* re.allchar) (str.to_re "public")))))))

(check-sat)
(exit)
