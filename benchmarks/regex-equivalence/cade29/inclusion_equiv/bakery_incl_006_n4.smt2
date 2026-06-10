;; Category : inclusion_equiv
;; Source   : CADE 29 b-armc-incl (bakery algorithm style)
;; Alternating tokens ⊆ any-order, n=4
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "inclusion_equiv")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.inter (re.++ (re.++ (str.to_re "a") (re.* (re.range "0" "9")) (str.to_re ";")) (re.++ (str.to_re "b") (re.* (re.range "0" "9")) (str.to_re ";")) (re.++ (str.to_re "a") (re.* (re.range "0" "9")) (str.to_re ";")) (re.++ (str.to_re "b") (re.* (re.range "0" "9")) (str.to_re ";"))) ((_ re.loop 4 4) (re.union (re.++ (str.to_re "a") (re.* (re.range "0" "9")) (str.to_re ";")) (re.++ (str.to_re "b") (re.* (re.range "0" "9")) (str.to_re ";"))))) (re.++ (re.++ (str.to_re "a") (re.* (re.range "0" "9")) (str.to_re ";")) (re.++ (str.to_re "b") (re.* (re.range "0" "9")) (str.to_re ";")) (re.++ (str.to_re "a") (re.* (re.range "0" "9")) (str.to_re ";")) (re.++ (str.to_re "b") (re.* (re.range "0" "9")) (str.to_re ";"))))))

(check-sat)
(exit)
