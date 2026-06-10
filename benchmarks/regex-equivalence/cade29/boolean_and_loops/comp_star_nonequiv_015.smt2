;; Category : boolean_and_loops
;; Source   : Boolean+star interaction
;; ¬(a*) ≢ (¬a)* (complement does not distribute over star)
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "boolean_and_loops")
(set-info :status sat)
(set-logic QF_S)

(assert (not (= (re.comp (re.* (str.to_re "a"))) (re.* (re.comp (str.to_re "a"))))))

(check-sat)
(exit)
