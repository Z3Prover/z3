;; Category : inclusion_equiv
;; Source   : CADE 29 b-armc-incl (producer-consumer style)
;; Balanced P-C ⊆ any-order, n=2
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "inclusion_equiv")
(set-info :status unsat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.inter ((_ re.loop 2 2) (re.++ (re.++ (str.to_re "P") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re ";")) (re.++ (str.to_re "C") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re ";")))) ((_ re.loop 4 4) (re.union (re.++ (str.to_re "P") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re ";")) (re.++ (str.to_re "C") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re ";"))))) (re.comp ((_ re.loop 2 2) (re.++ (re.++ (str.to_re "P") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re ";")) (re.++ (str.to_re "C") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re ";"))))))
      (re.inter (re.comp (re.inter ((_ re.loop 2 2) (re.++ (re.++ (str.to_re "P") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re ";")) (re.++ (str.to_re "C") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re ";")))) ((_ re.loop 4 4) (re.union (re.++ (str.to_re "P") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re ";")) (re.++ (str.to_re "C") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re ";")))))) ((_ re.loop 2 2) (re.++ (re.++ (str.to_re "P") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re ";")) (re.++ (str.to_re "C") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re ";"))))))))

(check-sat)
(exit)
