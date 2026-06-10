;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00139.smt2
;; Mutations:  intersect_no_slash_slash, union_to_inter
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
;; R2: mutated (intersect_no_slash_slash, union_to_inter)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "version") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "CodeguruBrowserwww.sogou.com\u{a}")) (re.comp (re.++ (str.to_re "version") (re.+ (re.inter(str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.inter (str.to_re "CodeguruBrowserwww.sogou.com\u{a}") (re.comp (re.++ re.all (str.to_re "//") re.all)))))) (re.inter (re.comp (re.++ (str.to_re "version") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "CodeguruBrowserwww.sogou.com\u{a}"))) (re.++ (str.to_re "version") (re.+ (re.inter(str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.inter (str.to_re "CodeguruBrowserwww.sogou.com\u{a}") (re.comp (re.++ re.all (str.to_re "//") re.all))))))))

(check-sat)
(exit)
