;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance10281.smt2
;; Mutations:  intersect_no_upper2, literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_upper2, literal_char_inc)
(assert
  (not
    (=
      (re.union (re.++ (re.opt (str.to_re "-")) (str.to_re "1000") (re.opt (re.++ (str.to_re ".") ((_ re.loop 1 3) (str.to_re "0"))))) (re.++ (re.opt (str.to_re "-")) ((_ re.loop 1 3) (re.range "0" "9"))) (re.++ (re.opt (str.to_re "-")) ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 1 3) (re.range "0" "9"))) (re.++ (re.opt (str.to_re "-")) (str.to_re "\u{a}.") ((_ re.loop 1 3) (re.range "0" "9"))))
      (re.union (re.++ (re.opt (str.to_re "-")) (str.to_re "1000") (re.opt (re.++ (str.to_re "/") ((_ re.loop 1 3) (str.to_re "0"))))) (re.++ (re.opt (str.to_re "-")) ((_ re.loop 1 3) (re.range "0" "9"))) (re.++ (re.inter (re.opt (str.to_re "-")) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 1 3) (re.range "0" "9"))) (re.++ (re.opt (str.to_re "-")) (str.to_re "\u{a}.") ((_ re.loop 1 3) (re.range "0" "9")))))))

(check-sat)
(exit)
