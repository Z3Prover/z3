;; Category : inclusion_equiv
;; Source   : CADE 29 b-armc-incl style
;; R ∪ R·R ⊆ R*: token
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "inclusion_equiv")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.inter (re.union (re.++ (str.to_re "[") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re "]")) (re.++ (re.++ (str.to_re "[") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re "]")) (re.++ (str.to_re "[") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re "]")))) (re.* (re.++ (str.to_re "[") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re "]")))) (re.union (re.++ (str.to_re "[") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re "]")) (re.++ (re.++ (str.to_re "[") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re "]")) (re.++ (str.to_re "[") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re "]")))))))

(check-sat)
(exit)
