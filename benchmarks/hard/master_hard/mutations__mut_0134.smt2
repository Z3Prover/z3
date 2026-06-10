;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance08444.smt2
;; Mutations:  intersect_no_digits4, intersect_no_spaces
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
;; R2: mutated (intersect_no_digits4, intersect_no_spaces)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "Referer:") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "HXDownload") (re.* re.allchar) (str.to_re "Referer:GREATDripline\u{a}")) (re.comp (re.++ (str.to_re "Referer:") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.inter (str.to_re "HXDownload") (re.comp (re.++ re.all (str.to_re " ") re.all))) (re.* re.allchar) (re.inter (str.to_re "Referer:GREATDripline\u{a}") (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all)))))) (re.inter (re.comp (re.++ (str.to_re "Referer:") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "HXDownload") (re.* re.allchar) (str.to_re "Referer:GREATDripline\u{a}"))) (re.++ (str.to_re "Referer:") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.inter (str.to_re "HXDownload") (re.comp (re.++ re.all (str.to_re " ") re.all))) (re.* re.allchar) (re.inter (str.to_re "Referer:GREATDripline\u{a}") (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all))))))))

(check-sat)
(exit)
