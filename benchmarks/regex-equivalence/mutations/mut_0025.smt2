;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance13512.smt2
;; Mutations:  intersect_ascii_printable_only, bound_lower_dec, intersect_no_slash_slash
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
;; R2: mutated (intersect_ascii_printable_only, bound_lower_dec, intersect_no_slash_slash)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ ((_ re.loop 4 4) (re.range "0" "9")) ((_ re.loop 0 2) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) ((_ re.loop 2 2) (re.union (re.range "a" "z") (re.range "A" "z"))) (str.to_re "\u{a}")) (re.comp (re.++ ((_ re.loop 4 4) (re.range "0" "9")) (re.inter ((_ re.loop 0 2) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.comp (re.++ re.all (str.to_re "//") re.all))) ((_ re.loop 1 2) (re.inter (re.union (re.range "a" "z") (re.range "A" "z")) (re.* (re.range " " "~")))) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ ((_ re.loop 4 4) (re.range "0" "9")) ((_ re.loop 0 2) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) ((_ re.loop 2 2) (re.union (re.range "a" "z") (re.range "A" "z"))) (str.to_re "\u{a}"))) (re.++ ((_ re.loop 4 4) (re.range "0" "9")) (re.inter ((_ re.loop 0 2) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.comp (re.++ re.all (str.to_re "//") re.all))) ((_ re.loop 1 2) (re.inter (re.union (re.range "a" "z") (re.range "A" "z")) (re.* (re.range " " "~")))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
