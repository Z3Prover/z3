;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance01162.smt2
;; Mutations:  range_shrink_hi, intersect_ascii_printable_only
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_hi, intersect_ascii_printable_only)
(assert
  (not
    (=
      (re.++ (str.to_re "hirmvtg/ggqh.kqh\u{1b}") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "whenu.com\u{13}") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "weatherHost:User-Agent:\u{a}"))
      (re.++ (re.inter (str.to_re "hirmvtg/ggqh.kqh\u{1b}") (re.* (re.range " " "~"))) (re.+ (re.union (re.range "0" "9") (re.range "A" "Y") (re.range "a" "z") (str.to_re "_"))) (str.to_re "whenu.com\u{13}") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "weatherHost:User-Agent:\u{a}")))))

(check-sat)
(exit)
