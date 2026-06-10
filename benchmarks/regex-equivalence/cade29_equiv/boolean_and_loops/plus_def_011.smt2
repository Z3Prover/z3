;; Category : boolean_and_loops
;; Source   : Kleene algebra
;; Plus definition: A+ ≡ A·A* [lower]
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "boolean_and_loops")
(set-info :status unsat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.+ (re.range "a" "z")) (re.comp (re.++ (re.range "a" "z") (re.* (re.range "a" "z")))))
      (re.inter (re.comp (re.+ (re.range "a" "z"))) (re.++ (re.range "a" "z") (re.* (re.range "a" "z")))))))

(check-sat)
(exit)
