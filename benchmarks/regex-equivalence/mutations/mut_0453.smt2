;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance12344.smt2
;; Mutations:  intersect_ascii_printable_only, star_to_plus
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
;; R2: mutated (intersect_ascii_printable_only, star_to_plus)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.* (re.union (re.++ (str.to_re "\u{5c}") re.allchar) (re.comp (str.to_re "\u{22}")))) (str.to_re "\u{a}")) (re.comp (re.++ (re.+ (re.union (re.inter (re.++ (str.to_re "\u{5c}") re.allchar) (re.* (re.range " " "~"))) (re.comp (str.to_re "\u{22}")))) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.* (re.union (re.++ (str.to_re "\u{5c}") re.allchar) (re.comp (str.to_re "\u{22}")))) (str.to_re "\u{a}"))) (re.++ (re.+ (re.union (re.inter (re.++ (str.to_re "\u{5c}") re.allchar) (re.* (re.range " " "~"))) (re.comp (str.to_re "\u{22}")))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
