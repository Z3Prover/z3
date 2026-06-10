;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance13746.smt2
;; Mutations:  range_shrink_lo
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo)
(assert
  (not
    (=
      (re.++ (str.to_re "hirmvtg/ggqh.kqh\u{1b}") (re.+ (re.range "0" "9")) (str.to_re "sports") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "whenu.com\u{13}wp-includes/feed.php?\u{a}"))
      (re.++ (str.to_re "hirmvtg/ggqh.kqh\u{1b}") (re.+ (re.range "0" "9")) (str.to_re "sports") (re.+ (re.union (re.range "0" "9") (re.range "B" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "whenu.com\u{13}wp-includes/feed.php?\u{a}")))))

(check-sat)
(exit)
