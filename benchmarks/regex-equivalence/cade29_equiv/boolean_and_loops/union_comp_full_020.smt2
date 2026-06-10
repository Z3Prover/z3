;; Category : boolean_and_loops
;; Source   : Boolean algebra
;; R∪¬R ≡ Σ*
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
      (re.inter (re.union (re.+ (re.range "0" "9")) (re.comp (re.+ (re.range "0" "9")))) (re.comp (re.* re.allchar)))
      (re.inter (re.comp (re.union (re.+ (re.range "0" "9")) (re.comp (re.+ (re.range "0" "9"))))) (re.* re.allchar)))))

(check-sat)
(exit)
