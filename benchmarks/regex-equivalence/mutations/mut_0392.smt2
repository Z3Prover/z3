;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance03679.smt2
;; Mutations:  intersect_ascii_printable_only, star_to_plus, literal_char_inc
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
;; R2: mutated (intersect_ascii_printable_only, star_to_plus, literal_char_inc)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "/From:") (re.* (re.union (str.to_re "\u{d}") (str.to_re "\u{a}"))) (str.to_re "SpyBuddy/smi\u{a}")) (re.comp (re.++ (str.to_re "/From;") (re.+ (re.inter (re.union (str.to_re "\u{d}") (str.to_re "\u{a}")) (re.* (re.range " " "~")))) (str.to_re "SpyBuddy/smi\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "/From:") (re.* (re.union (str.to_re "\u{d}") (str.to_re "\u{a}"))) (str.to_re "SpyBuddy/smi\u{a}"))) (re.++ (str.to_re "/From;") (re.+ (re.inter (re.union (str.to_re "\u{d}") (str.to_re "\u{a}")) (re.* (re.range " " "~")))) (str.to_re "SpyBuddy/smi\u{a}"))))))

(check-sat)
(exit)
