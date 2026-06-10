;; Category : regexlib_equiv
;; Source   : RegExLib password patterns
;; With vs without lowercase requirement
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "regexlib_equiv")
(set-info :status sat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.inter (re.inter (re.++ (re.* re.allchar) (re.range "0" "9") (re.* re.allchar)) (re.++ (re.* re.allchar) (re.range "A" "Z") (re.* re.allchar))) ((_ re.loop 8 20) (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (re.union (str.to_re "!") (str.to_re "@") (str.to_re "#") (str.to_re "$") (str.to_re "%"))))) (re.comp (re.inter (re.inter (re.++ (re.* re.allchar) (re.range "0" "9") (re.* re.allchar)) (re.++ (re.* re.allchar) (re.range "A" "Z") (re.* re.allchar))) (re.inter (re.++ (re.* re.allchar) (re.range "a" "z") (re.* re.allchar)) ((_ re.loop 8 20) (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (re.union (str.to_re "!") (str.to_re "@") (str.to_re "#") (str.to_re "$") (str.to_re "%"))))))))
      (re.inter (re.comp (re.inter (re.inter (re.++ (re.* re.allchar) (re.range "0" "9") (re.* re.allchar)) (re.++ (re.* re.allchar) (re.range "A" "Z") (re.* re.allchar))) ((_ re.loop 8 20) (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (re.union (str.to_re "!") (str.to_re "@") (str.to_re "#") (str.to_re "$") (str.to_re "%")))))) (re.inter (re.inter (re.++ (re.* re.allchar) (re.range "0" "9") (re.* re.allchar)) (re.++ (re.* re.allchar) (re.range "A" "Z") (re.* re.allchar))) (re.inter (re.++ (re.* re.allchar) (re.range "a" "z") (re.* re.allchar)) ((_ re.loop 8 20) (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (re.union (str.to_re "!") (str.to_re "@") (str.to_re "#") (str.to_re "$") (str.to_re "%"))))))))))

(check-sat)
(exit)
