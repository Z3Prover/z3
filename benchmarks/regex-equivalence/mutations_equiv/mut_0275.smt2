;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11054.smt2
;; Mutations:  intersect_no_digits4, literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_digits4, literal_char_inc)
(assert
  (not
    (=
      (re.union (re.++ (str.to_re "100") (re.opt (re.++ (str.to_re ".") ((_ re.loop 0 2) (str.to_re "0"))))) (re.++ ((_ re.loop 0 2) (re.range "0" "9")) (re.opt (re.++ (str.to_re ".") ((_ re.loop 0 2) (re.range "0" "9")))) (str.to_re "\u{a}")))
      (re.union (re.++ (str.to_re "100") (re.opt (re.++ (str.to_re ".") ((_ re.loop 0 2) (str.to_re "1"))))) (re.++ ((_ re.loop 0 2) (re.range "0" "9")) (re.opt (re.++ (str.to_re ".") (re.inter ((_ re.loop 0 2) (re.range "0" "9")) (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all))))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
