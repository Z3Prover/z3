;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance13096.smt2
;; Mutations:  union_to_inter, intersect_no_digits4
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (union_to_inter, intersect_no_digits4)
(assert
  (not
    (=
      (re.++ (str.to_re "www.cameup.com\u{13}") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "spyblini.ini\u{a}"))
      (re.++ (re.inter (str.to_re "www.cameup.com\u{13}") (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all))) (re.+ (re.inter (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "spyblini.ini\u{a}")))))

(check-sat)
(exit)
