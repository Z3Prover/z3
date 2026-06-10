;; Category : parametric
;; Source   : Constructed (character class ordering)
;; (.*\w\s.*){2} vs (.*\s\w.*){2} (inequivalent)
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "parametric")
(set-info :status sat)
(set-logic QF_S)

(assert (not (= ((_ re.loop 2 2) (re.++ (re.* re.allchar) (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "_")) (re.union (str.to_re " ") (str.to_re "\t") (str.to_re "\n") (str.to_re "\r")) (re.* re.allchar))) ((_ re.loop 2 2) (re.++ (re.* re.allchar) (re.union (str.to_re " ") (str.to_re "\t") (str.to_re "\n") (str.to_re "\r")) (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "_")) (re.* re.allchar))))))

(check-sat)
(exit)
