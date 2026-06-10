;; Category : Phone numbers
;; Benchmark: phone_us_dashes vs phone_us_dots
;; R1: US with dashes: ddd-ddd-dddd
;; R2: US with dots: ddd.ddd.dddd
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "phone")
(set-info :status sat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 4 4) (re.range "0" "9"))) (re.comp (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 4 4) (re.range "0" "9")))))
      (re.inter (re.comp (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 4 4) (re.range "0" "9")))) (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 4 4) (re.range "0" "9")))))))

(check-sat)
(exit)
