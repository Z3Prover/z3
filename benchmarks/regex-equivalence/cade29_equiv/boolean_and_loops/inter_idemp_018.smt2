;; Category : boolean_and_loops
;; Source   : Boolean algebra
;; Idempotence: R∩R ≡ R
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
      (re.inter (re.inter (re.++ (re.* (re.range "0" "9")) (str.to_re "-") (re.* (re.union (re.range "a" "z") (re.range "A" "Z")))) (re.++ (re.* (re.range "0" "9")) (str.to_re "-") (re.* (re.union (re.range "a" "z") (re.range "A" "Z"))))) (re.comp (re.++ (re.* (re.range "0" "9")) (str.to_re "-") (re.* (re.union (re.range "a" "z") (re.range "A" "Z"))))))
      (re.inter (re.comp (re.inter (re.++ (re.* (re.range "0" "9")) (str.to_re "-") (re.* (re.union (re.range "a" "z") (re.range "A" "Z")))) (re.++ (re.* (re.range "0" "9")) (str.to_re "-") (re.* (re.union (re.range "a" "z") (re.range "A" "Z")))))) (re.++ (re.* (re.range "0" "9")) (str.to_re "-") (re.* (re.union (re.range "a" "z") (re.range "A" "Z"))))))))

(check-sat)
(exit)
