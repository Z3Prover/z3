;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance01025.smt2
;; Mutations:  range_shrink_lo
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo)
(assert
  (not
    (=
      (re.++ (re.* re.allchar) (re.union (str.to_re "$") (str.to_re "S") (str.to_re "s")) (str.to_re "pecia") (re.union (str.to_re "l") (str.to_re "1")) (re.comp (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (re.union (str.to_re "O") (str.to_re "o") (str.to_re "0")) (str.to_re "ffer") (re.* re.allchar) (str.to_re "\u{a}"))
      (re.++ (re.* re.allchar) (re.union (str.to_re "$") (str.to_re "S") (str.to_re "s")) (str.to_re "pecia") (re.union (str.to_re "l") (str.to_re "1")) (re.comp (re.union (re.range "1" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (re.union (str.to_re "O") (str.to_re "o") (str.to_re "0")) (str.to_re "ffer") (re.* re.allchar) (str.to_re "\u{a}")))))

(check-sat)
(exit)
