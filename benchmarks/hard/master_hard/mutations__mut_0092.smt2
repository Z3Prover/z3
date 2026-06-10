;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance12828.smt2
;; Mutations:  union_to_inter, intersect_no_digits4, intersect_no_digits4
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
;; R2: mutated (union_to_inter, intersect_no_digits4, intersect_no_digits4)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "toolbarplace.com") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "Server") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "X-Mailer:\u{13}") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "User-Agent:Host:Bar/newsurfer4/\u{a}")) (re.comp (re.++ (re.inter (str.to_re "toolbarplace.com") (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all))) (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (re.inter (str.to_re "Server") (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all))) (re.* (re.inter(str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "X-Mailer:\u{13}") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "User-Agent:Host:Bar/newsurfer4/\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "toolbarplace.com") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "Server") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "X-Mailer:\u{13}") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "User-Agent:Host:Bar/newsurfer4/\u{a}"))) (re.++ (re.inter (str.to_re "toolbarplace.com") (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all))) (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (re.inter (str.to_re "Server") (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all))) (re.* (re.inter(str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "X-Mailer:\u{13}") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "User-Agent:Host:Bar/newsurfer4/\u{a}"))))))

(check-sat)
(exit)
