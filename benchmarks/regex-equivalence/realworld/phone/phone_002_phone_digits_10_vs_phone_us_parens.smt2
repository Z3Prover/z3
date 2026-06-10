;; Category : Phone numbers
;; Benchmark: phone_digits_10 vs phone_us_parens
;; R1: Plain 10 digits: d{10}
;; R2: US with parens: (ddd) ddd-dddd
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "phone")
(set-info :status sat)
(set-logic QF_S)

(declare-const x String)

(assert
  (str.in_re x
    (re.union (re.inter ((_ re.loop 10 10) (re.range "0" "9")) (re.comp (re.++ (str.to_re "(") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ")") (re.opt (str.to_re " ")) ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 4 4) (re.range "0" "9"))))) (re.inter (re.comp ((_ re.loop 10 10) (re.range "0" "9"))) (re.++ (str.to_re "(") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ")") (re.opt (str.to_re " ")) ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 4 4) (re.range "0" "9")))))))

(check-sat)
(exit)
