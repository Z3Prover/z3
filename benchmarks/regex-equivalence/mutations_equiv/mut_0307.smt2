;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00748.smt2
;; Mutations:  intersect_no_spaces, range_shrink_lo
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_spaces, range_shrink_lo)
(assert
  (not
    (=
      (re.++ (str.to_re "com") (re.range "0" "9") (str.to_re "search.conduit.com") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "User-Agent:\u{a}"))
      (re.++ (str.to_re "com") (re.range "1" "9") (str.to_re "search.conduit.com") (re.+ (re.inter (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.comp (re.++ re.all (str.to_re " ") re.all)))) (str.to_re "User-Agent:\u{a}")))))

(check-sat)
(exit)
