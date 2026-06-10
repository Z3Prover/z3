;; Category : CSS colors
;; Benchmark: css_hex3 vs css_rgb_func
;; R1: Short hex color: #[0-9a-fA-F]{3}
;; R2: rgb(r,g,b) function notation
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "css")
(set-info :status sat)
(set-logic QF_S)

(declare-const x String)

(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "#") ((_ re.loop 3 3) (re.union (re.range "0" "9") (re.range "a" "f") (re.range "A" "F")))) (re.comp (re.++ (str.to_re "rgb(") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ",") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ",") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ")")))) (re.inter (re.comp (re.++ (str.to_re "#") ((_ re.loop 3 3) (re.union (re.range "0" "9") (re.range "a" "f") (re.range "A" "F"))))) (re.++ (str.to_re "rgb(") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ",") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ",") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ")"))))))

(check-sat)
(exit)
