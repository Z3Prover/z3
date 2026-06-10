;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance04782.smt2
;; Mutations:  intersect_max_len_10, intersect_no_slash_slash
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_max_len_10, intersect_no_slash_slash)
(assert
  (not
    (=
      (re.union (re.++ (re.opt (re.++ (str.to_re ".") ((_ re.loop 0 2) (re.range "0" "9")))) (re.opt ((_ re.loop 1 1) (str.to_re "0"))) (re.opt (re.range "0" "3"))) (re.++ (str.to_re "4") (re.opt (re.++ (str.to_re ".") ((_ re.loop 1 2) (str.to_re "0"))))) (re.++ (re.opt (str.to_re ".")) (str.to_re "\u{a}") (re.opt ((_ re.loop 1 1) (str.to_re "0"))) (re.opt (re.range "0" "4"))))
      (re.union (re.++ (re.opt (re.inter (re.++ (str.to_re ".") ((_ re.loop 0 2) (re.range "0" "9"))) (re.comp (re.++ re.all (str.to_re "//") re.all)))) (re.inter (re.opt ((_ re.loop 1 1) (str.to_re "0"))) ((_ re.loop 0 10) re.allchar)) (re.opt (re.range "0" "3"))) (re.++ (str.to_re "4") (re.opt (re.++ (str.to_re ".") ((_ re.loop 1 2) (str.to_re "0"))))) (re.++ (re.opt (str.to_re ".")) (str.to_re "\u{a}") (re.opt ((_ re.loop 1 1) (str.to_re "0"))) (re.opt (re.range "0" "4")))))))

(check-sat)
(exit)
