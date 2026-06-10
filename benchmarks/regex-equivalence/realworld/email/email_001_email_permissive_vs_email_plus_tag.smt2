;; Category : Email validation
;; Benchmark: email_permissive vs email_plus_tag
;; R1: Permissive: [a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+.[a-zA-Z]{2,10}
;; R2: Explicit plus-tag: local(+tag)?@domain.tld
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "email")
(set-info :status sat)
(set-logic QF_S)

(declare-const x String)

(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "_") (str.to_re "%") (str.to_re "-") (str.to_re "+"))) (str.to_re "@") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "-"))) (str.to_re ".") ((_ re.loop 2 10) (re.union (re.range "a" "z") (re.range "A" "Z")))) (re.comp (re.++ (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "_") (str.to_re "-"))) (re.opt (re.++ (str.to_re "+") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "_") (str.to_re "-"))))) (str.to_re "@") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "-"))) (str.to_re ".") ((_ re.loop 2 6) (re.union (re.range "a" "z") (re.range "A" "Z")))))) (re.inter (re.comp (re.++ (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "_") (str.to_re "%") (str.to_re "-") (str.to_re "+"))) (str.to_re "@") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "-"))) (str.to_re ".") ((_ re.loop 2 10) (re.union (re.range "a" "z") (re.range "A" "Z"))))) (re.++ (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "_") (str.to_re "-"))) (re.opt (re.++ (str.to_re "+") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "_") (str.to_re "-"))))) (str.to_re "@") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "-"))) (str.to_re ".") ((_ re.loop 2 6) (re.union (re.range "a" "z") (re.range "A" "Z"))))))))

(check-sat)
(exit)
