;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance15994.smt2
;; Mutations:  range_expand_hi, range_shrink_lo, range_shrink_hi
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_expand_hi, range_shrink_lo, range_shrink_hi)
(assert
  (not
    (=
      (re.++ (re.range "1" "9") ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re " ")) (re.union ((_ re.loop 2 2) (re.union (re.range "a" "r") (re.range "t" "z") (re.range "A" "R") (re.range "T" "Z"))) (re.++ (re.union (str.to_re "s") (str.to_re "S")) (re.union (str.to_re "d") (str.to_re "a") (str.to_re "s") (str.to_re "D") (str.to_re "A") (str.to_re "S")))) (str.to_re "\u{a}"))
      (re.++ (re.range "1" "8") ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re " ")) (re.union ((_ re.loop 2 2) (re.union (re.range "a" "r") (re.range "u" "z") (re.range "A" "S") (re.range "T" "Z"))) (re.++ (re.union (str.to_re "s") (str.to_re "S")) (re.union (str.to_re "d") (str.to_re "a") (str.to_re "s") (str.to_re "D") (str.to_re "A") (str.to_re "S")))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
