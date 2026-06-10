;; Category : CSS colors
;; Benchmark: css_hex6_lower vs css_rgb_func
;; R1: Lowercase-only hex: #[0-9a-f]{6}
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
    (re.union (re.inter (re.++ (str.to_re "#") ((_ re.loop 6 6) (re.union (re.range "0" "9") (re.range "a" "f")))) (re.comp (re.++ (str.to_re "rgb(") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ",") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ",") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ")")))) (re.inter (re.comp (re.++ (str.to_re "#") ((_ re.loop 6 6) (re.union (re.range "0" "9") (re.range "a" "f"))))) (re.++ (str.to_re "rgb(") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ",") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ",") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ")"))))))

(check-sat)
(exit)
