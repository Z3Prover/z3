;; Category : boolean_and_loops
;; Source   : Kleene algebra
;; Star unrolling: A* ≡ ε∪A·A* [alpha]
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "boolean_and_loops")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.* (re.union (re.range "a" "z") (re.range "A" "Z"))) (re.union (str.to_re "") (re.++ (re.union (re.range "a" "z") (re.range "A" "Z")) (re.* (re.union (re.range "a" "z") (re.range "A" "Z"))))))))

(check-sat)
(exit)
