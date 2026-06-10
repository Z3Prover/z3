;; Category : parametric
;; Source   : Constructed (complement chain)
;; ¬^{2·8}(R) ≡ R (complement chain depth 16)
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "parametric")
(set-info :status unsat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.++ (re.* (re.range "0" "9")) (str.to_re "-") (re.* (re.union (re.range "a" "z") (re.range "A" "Z")))))))))))))))))))) (re.comp (re.++ (re.* (re.range "0" "9")) (str.to_re "-") (re.* (re.union (re.range "a" "z") (re.range "A" "Z"))))))
      (re.inter (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.comp (re.++ (re.* (re.range "0" "9")) (str.to_re "-") (re.* (re.union (re.range "a" "z") (re.range "A" "Z"))))))))))))))))))))) (re.++ (re.* (re.range "0" "9")) (str.to_re "-") (re.* (re.union (re.range "a" "z") (re.range "A" "Z"))))))))

(check-sat)
(exit)
