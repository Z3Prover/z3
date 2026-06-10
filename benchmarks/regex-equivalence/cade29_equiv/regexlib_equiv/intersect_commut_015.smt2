;; Category : regexlib_equiv
;; Source   : Constructed from RegExLib patterns
;; Commutativity of ∩: zip+hasdash
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
      (re.inter (re.inter (re.union ((_ re.loop 5 5) (re.range "0" "9")) (re.++ ((_ re.loop 5 5) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 4 4) (re.range "0" "9")))) (re.++ (re.* re.allchar) (str.to_re "-") (re.* re.allchar))) (re.comp (re.inter (re.++ (re.* re.allchar) (str.to_re "-") (re.* re.allchar)) (re.union ((_ re.loop 5 5) (re.range "0" "9")) (re.++ ((_ re.loop 5 5) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 4 4) (re.range "0" "9")))))))
      (re.inter (re.comp (re.inter (re.union ((_ re.loop 5 5) (re.range "0" "9")) (re.++ ((_ re.loop 5 5) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 4 4) (re.range "0" "9")))) (re.++ (re.* re.allchar) (str.to_re "-") (re.* re.allchar)))) (re.inter (re.++ (re.* re.allchar) (str.to_re "-") (re.* re.allchar)) (re.union ((_ re.loop 5 5) (re.range "0" "9")) (re.++ ((_ re.loop 5 5) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 4 4) (re.range "0" "9")))))))))

(check-sat)
(exit)
