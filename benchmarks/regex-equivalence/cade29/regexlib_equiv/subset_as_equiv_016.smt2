;; Category : regexlib_equiv
;; Source   : RegExLib email subset
;; Subset: single-segment ∩ multi-segment ≡ single-segment
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "regexlib_equiv")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.inter (re.++ (re.+ (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (re.union (str.to_re "_") (str.to_re ".") (str.to_re "-")))) (str.to_re "@") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re ".") ((_ re.loop 2 6) (re.union (re.range "a" "z") (re.range "A" "Z")))) (re.++ (re.+ (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (re.union (str.to_re "_") (str.to_re ".") (str.to_re "-")))) (str.to_re "@") (re.+ (re.++ (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re "."))) ((_ re.loop 2 6) (re.union (re.range "a" "z") (re.range "A" "Z"))))) (re.++ (re.+ (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (re.union (str.to_re "_") (str.to_re ".") (str.to_re "-")))) (str.to_re "@") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (str.to_re ".") ((_ re.loop 2 6) (re.union (re.range "a" "z") (re.range "A" "Z")))))))

(check-sat)
(exit)
