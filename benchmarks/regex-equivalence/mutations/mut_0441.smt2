;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance03257.smt2
;; Mutations:  intersect_min_len_5, union_to_inter, plus_to_star
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
;; R2: mutated (intersect_min_len_5, union_to_inter, plus_to_star)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re ".exe") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "v2.0") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "smrtshpr-cs-\u{13}\u{a}")) (re.comp (re.++ (str.to_re ".exe") (re.* (re.inter(str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "v2.0") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.inter (str.to_re "smrtshpr-cs-\u{13}\u{a}") (re.++ ((_ re.loop 5 5) re.allchar) re.all))))) (re.inter (re.comp (re.++ (str.to_re ".exe") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "v2.0") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "smrtshpr-cs-\u{13}\u{a}"))) (re.++ (str.to_re ".exe") (re.* (re.inter(str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "v2.0") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.inter (str.to_re "smrtshpr-cs-\u{13}\u{a}") (re.++ ((_ re.loop 5 5) re.allchar) re.all)))))))

(check-sat)
(exit)
