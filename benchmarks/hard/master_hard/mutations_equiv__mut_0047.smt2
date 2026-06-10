;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance09099.smt2
;; Mutations:  bound_upper_dec, range_expand_hi
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (bound_upper_dec, range_expand_hi)
(assert
  (not
    (=
      (re.++ (re.union (str.to_re "::") (re.++ ((_ re.loop 7 7) (re.++ ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))) (str.to_re ":"))) ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9")))) (re.++ (str.to_re ":") ((_ re.loop 1 6) (re.++ (str.to_re ":") ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9")))))) (re.++ ((_ re.loop 1 6) (re.++ ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))) (str.to_re ":"))) (str.to_re ":")) (re.++ ((_ re.loop 1 6) (re.++ (str.to_re ":") ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))))) ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))) (str.to_re ":")) (re.++ ((_ re.loop 2 2) (re.++ ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))) (str.to_re ":"))) ((_ re.loop 1 5) (re.++ (str.to_re ":") ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9")))))) (re.++ ((_ re.loop 3 3) (re.++ ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))) (str.to_re ":"))) ((_ re.loop 1 4) (re.++ (str.to_re ":") ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9")))))) (re.++ ((_ re.loop 4 4) (re.++ ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))) (str.to_re ":"))) ((_ re.loop 1 3) (re.++ (str.to_re ":") ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9")))))) (re.++ ((_ re.loop 5 5) (re.++ ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))) (str.to_re ":"))) ((_ re.loop 1 2) (re.++ (str.to_re ":") ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))))))) (str.to_re "\u{a}"))
      (re.++ (re.union (str.to_re "::") (re.++ ((_ re.loop 7 7) (re.++ ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" ":"))) (str.to_re ":"))) ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9")))) (re.++ (str.to_re ":") ((_ re.loop 1 6) (re.++ (str.to_re ":") ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9")))))) (re.++ ((_ re.loop 1 6) (re.++ ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))) (str.to_re ":"))) (str.to_re ":")) (re.++ ((_ re.loop 1 6) (re.++ (str.to_re ":") ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))))) ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))) (str.to_re ":")) (re.++ ((_ re.loop 2 2) (re.++ ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))) (str.to_re ":"))) ((_ re.loop 1 5) (re.++ (str.to_re ":") ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9")))))) (re.++ ((_ re.loop 3 3) (re.++ ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))) (str.to_re ":"))) ((_ re.loop 1 4) (re.++ (str.to_re ":") ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9")))))) (re.++ ((_ re.loop 4 4) (re.++ ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))) (str.to_re ":"))) ((_ re.loop 1 3) (re.++ (str.to_re ":") ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9")))))) (re.++ ((_ re.loop 5 5) (re.++ ((_ re.loop 1 3) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))) (str.to_re ":"))) ((_ re.loop 1 2) (re.++ (str.to_re ":") ((_ re.loop 1 4) (re.union (re.range "a" "f") (re.range "A" "F") (re.range "0" "9"))))))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
