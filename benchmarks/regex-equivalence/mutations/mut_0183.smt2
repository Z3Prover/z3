;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance09868.smt2
;; Mutations:  literal_char_inc, intersect_min_len_5, intersect_ascii_printable_only
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
;; R2: mutated (literal_char_inc, intersect_min_len_5, intersect_ascii_printable_only)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "/Cookie:") (re.opt (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "SECID=") (re.+ (re.comp (str.to_re ";"))) (str.to_re "/mD\u{a}")) (re.comp (re.++ (re.inter (str.to_re "/Cookie:") (re.* (re.range " " "~"))) (re.inter (re.opt (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.++ ((_ re.loop 5 5) re.allchar) re.all)) (str.to_re "SECID=") (re.+ (re.comp (str.to_re "<"))) (str.to_re "/mD\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "/Cookie:") (re.opt (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "SECID=") (re.+ (re.comp (str.to_re ";"))) (str.to_re "/mD\u{a}"))) (re.++ (re.inter (str.to_re "/Cookie:") (re.* (re.range " " "~"))) (re.inter (re.opt (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.++ ((_ re.loop 5 5) re.allchar) re.all)) (str.to_re "SECID=") (re.+ (re.comp (str.to_re "<"))) (str.to_re "/mD\u{a}"))))))

(check-sat)
(exit)
