;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance01039.smt2
;; Mutations:  intersect_no_dot_dot, intersect_no_dot_dot
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_dot_dot, intersect_no_dot_dot)
(assert
  (not
    (=
      (re.++ (str.to_re "select/Get") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "Host:") (re.* re.allchar) (str.to_re "ppcdomain.co.uk\u{a}"))
      (re.++ (re.inter (str.to_re "select/Get") (re.comp (re.++ re.all (str.to_re "..") re.all))) (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "Host:") (re.* re.allchar) (re.inter (str.to_re "ppcdomain.co.uk\u{a}") (re.comp (re.++ re.all (str.to_re "..") re.all)))))))

(check-sat)
(exit)
