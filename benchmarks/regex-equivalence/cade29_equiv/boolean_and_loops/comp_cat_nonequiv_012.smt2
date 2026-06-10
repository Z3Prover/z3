;; Category : boolean_and_loops
;; Source   : Boolean+concat interaction
;; ¬(A·B) ≢ ¬A·¬B (complement does not distribute over concat)
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "boolean_and_loops")
(set-info :status sat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.comp (re.++ (re.range "0" "9") (re.range "a" "z"))) (re.comp (re.++ (re.comp (re.range "0" "9")) (re.comp (re.range "a" "z")))))
      (re.inter (re.comp (re.comp (re.++ (re.range "0" "9") (re.range "a" "z")))) (re.++ (re.comp (re.range "0" "9")) (re.comp (re.range "a" "z")))))))

(check-sat)
(exit)
