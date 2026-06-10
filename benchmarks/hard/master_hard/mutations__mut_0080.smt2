;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance02027.smt2
;; Mutations:  intersect_no_dot_dot, intersect_ascii_printable_only, literal_char_inc
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
;; R2: mutated (intersect_no_dot_dot, intersect_ascii_printable_only, literal_char_inc)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "/filename=") (re.opt (re.union (str.to_re "\u{22}") (str.to_re "'"))) (re.* (re.comp (str.to_re "\u{a}"))) (str.to_re ".motn") (re.union (str.to_re "\u{22}") (str.to_re "'") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "/si\u{a}")) (re.comp (re.++ (str.to_re "/filename>") (re.opt (re.union (re.inter (str.to_re "\u{22}") (re.* (re.range " " "~"))) (str.to_re "'"))) (re.inter (re.* (re.comp (str.to_re "\u{a}"))) (re.comp (re.++ re.all (str.to_re "..") re.all))) (str.to_re ".motn") (re.union (str.to_re "\u{22}") (str.to_re "'") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "/si\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "/filename=") (re.opt (re.union (str.to_re "\u{22}") (str.to_re "'"))) (re.* (re.comp (str.to_re "\u{a}"))) (str.to_re ".motn") (re.union (str.to_re "\u{22}") (str.to_re "'") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "/si\u{a}"))) (re.++ (str.to_re "/filename>") (re.opt (re.union (re.inter (str.to_re "\u{22}") (re.* (re.range " " "~"))) (str.to_re "'"))) (re.inter (re.* (re.comp (str.to_re "\u{a}"))) (re.comp (re.++ re.all (str.to_re "..") re.all))) (str.to_re ".motn") (re.union (str.to_re "\u{22}") (str.to_re "'") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "/si\u{a}"))))))

(check-sat)
(exit)
