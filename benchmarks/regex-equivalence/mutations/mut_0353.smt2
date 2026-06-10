;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11103.smt2
;; Mutations:  intersect_min_len_5, literal_char_dec
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
;; R2: mutated (intersect_min_len_5, literal_char_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "forum=") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "/toolbar/ico/\u{a}")) (re.comp (re.++ (str.to_re "forum<") (re.inter (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.++ ((_ re.loop 5 5) re.allchar) re.all)) (str.to_re "/toolbar/ico/\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "forum=") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "/toolbar/ico/\u{a}"))) (re.++ (str.to_re "forum<") (re.inter (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.++ ((_ re.loop 5 5) re.allchar) re.all)) (str.to_re "/toolbar/ico/\u{a}"))))))

(check-sat)
(exit)
