;; Category : regexlib_equiv
;; Source   : Constructed from RegExLib patterns
;; Commutativity of ∩: digit+upper
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "regexlib_equiv")
(set-info :status unsat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.inter (re.++ (re.* re.allchar) (re.range "0" "9") (re.* re.allchar)) (re.++ (re.* re.allchar) (re.range "A" "Z") (re.* re.allchar))) (re.comp (re.inter (re.++ (re.* re.allchar) (re.range "A" "Z") (re.* re.allchar)) (re.++ (re.* re.allchar) (re.range "0" "9") (re.* re.allchar)))))
      (re.inter (re.comp (re.inter (re.++ (re.* re.allchar) (re.range "0" "9") (re.* re.allchar)) (re.++ (re.* re.allchar) (re.range "A" "Z") (re.* re.allchar)))) (re.inter (re.++ (re.* re.allchar) (re.range "A" "Z") (re.* re.allchar)) (re.++ (re.* re.allchar) (re.range "0" "9") (re.* re.allchar)))))))

(check-sat)
(exit)
