;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance12789.smt2
;; Mutations:  literal_char_inc, range_shrink_lo, range_expand_hi
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_inc, range_shrink_lo, range_expand_hi)
(assert
  (not
    (=
      (re.++ (re.opt (re.++ (re.union (re.range "a" "z") (re.range "A" "Z")) (str.to_re ":") (re.* (re.++ (str.to_re "\u{5c}") (re.+ (str.to_re "w")))) (str.to_re "\u{5c}") (re.+ (re.union (re.range "a" "z") (re.range "A" "Z") (str.to_re "0") (str.to_re "_") (str.to_re "9"))))) re.allchar (str.to_re "xls\u{a}"))
      (re.++ (re.opt (re.++ (re.union (re.range "a" "z") (re.range "A" "[")) (str.to_re ":") (re.* (re.++ (str.to_re "\u{5c}") (re.+ (str.to_re "w")))) (str.to_re "\u{5c}") (re.+ (re.union (re.range "b" "z") (re.range "A" "Z") (str.to_re "0") (str.to_re "`") (str.to_re "9"))))) re.allchar (str.to_re "xls\u{a}")))))

(check-sat)
(exit)
