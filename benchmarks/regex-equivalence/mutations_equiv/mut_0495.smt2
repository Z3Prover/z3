;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance13727.smt2
;; Mutations:  range_shrink_lo, intersect_no_spaces, opt_to_required
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo, intersect_no_spaces, opt_to_required)
(assert
  (not
    (=
      (re.union (re.++ (re.opt (re.range "0" "2")) ((_ re.loop 1 1) (re.range "0" "3")) (re.opt (re.++ (str.to_re ".") ((_ re.loop 1 2) (re.range "0" "9"))))) (re.++ (re.opt (re.range "0" "1")) ((_ re.loop 1 1) (re.range "0" "9")) (re.opt (re.++ (str.to_re ".") ((_ re.loop 1 2) (re.range "0" "9"))))) (re.++ (re.opt (str.to_re "-")) (str.to_re "24") (re.opt (re.++ (str.to_re ".") ((_ re.loop 1 2) (str.to_re "0"))))) (re.++ ((_ re.loop 1 1) (re.range "0" "9")) (re.opt (re.++ (str.to_re ".") ((_ re.loop 1 2) (re.range "0" "9")))) (str.to_re "\u{a}")))
      (re.union (re.++ re.range "0" "2") ((_ re.loop 1 1) (re.range "0" "3")) (re.opt (re.inter (re.++ (str.to_re ".") ((_ re.loop 1 2) (re.range "0" "9"))) (re.comp (re.++ re.all (str.to_re " ") re.all))))))))

(check-sat)
(exit)
