;; Category : regexlib_equiv
;; Source   : RegExLib date patterns
;; Date MM/DD/YYYY vs MM/DD/YYYY
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "regexlib_equiv")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ (re.++ (re.opt (re.union (str.to_re "0") (str.to_re "1"))) (re.range "0" "9")) (str.to_re "/") (re.++ (re.opt (re.union (str.to_re "0") (str.to_re "1") (str.to_re "2") (str.to_re "3"))) (re.range "0" "9")) (str.to_re "/") ((_ re.loop 4 4) (re.range "0" "9"))) (re.++ (re.++ (re.opt (re.union (str.to_re "0") (str.to_re "1"))) (re.range "0" "9")) (str.to_re "/") (re.++ (re.opt (re.union (str.to_re "0") (str.to_re "1") (str.to_re "2") (str.to_re "3"))) (re.range "0" "9")) (str.to_re "/") ((_ re.loop 4 4) (re.range "0" "9"))))))

(check-sat)
(exit)
