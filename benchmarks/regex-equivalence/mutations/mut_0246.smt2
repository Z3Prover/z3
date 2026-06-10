;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance12404.smt2
;; Mutations:  intersect_no_alnum5
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
;; R2: mutated (intersect_no_alnum5)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "CUSTOM") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "www.locators.comas.starware.com\u{a}")) (re.comp (re.++ (str.to_re "CUSTOM") (re.inter (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.comp (re.++ re.all ((_ re.loop 5 5) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) re.all))) (str.to_re "www.locators.comas.starware.com\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "CUSTOM") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "www.locators.comas.starware.com\u{a}"))) (re.++ (str.to_re "CUSTOM") (re.inter (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.comp (re.++ re.all ((_ re.loop 5 5) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) re.all))) (str.to_re "www.locators.comas.starware.com\u{a}"))))))

(check-sat)
(exit)
