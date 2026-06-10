;; Category : Phone numbers
;; Benchmark: phone_us_dots vs phone_e164
;; R1: US with dots: ddd.ddd.dddd
;; R2: E.164 international: +d{1,15}
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
    (re.union (re.inter (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 4 4) (re.range "0" "9"))) (re.comp (re.++ (str.to_re "+") ((_ re.loop 1 15) (re.range "0" "9"))))) (re.inter (re.comp (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 4 4) (re.range "0" "9")))) (re.++ (str.to_re "+") ((_ re.loop 1 15) (re.range "0" "9")))))))

(check-sat)
(exit)
