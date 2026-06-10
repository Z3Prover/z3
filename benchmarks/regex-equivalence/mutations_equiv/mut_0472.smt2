;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance15843.smt2
;; Mutations:  intersect_no_alnum5, literal_char_dec, union_to_inter
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_alnum5, literal_char_dec, union_to_inter)
(assert
  (not
    (=
      (re.union (re.++ (str.to_re "6011") ((_ re.loop 12 12) (re.range "0" "9"))) (re.++ (str.to_re "\u{a}65") ((_ re.loop 14 14) (re.range "0" "9"))))
      (re.inter (re.++ (str.to_re "6010") ((_ re.loop 12 12) (re.range "0" "9"))) (re.inter (re.++ (str.to_re "\u{a}65") ((_ re.loop 14 14) (re.range "0" "9"))) (re.comp (re.++ re.all ((_ re.loop 5 5) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) re.all)))))))

(check-sat)
(exit)
