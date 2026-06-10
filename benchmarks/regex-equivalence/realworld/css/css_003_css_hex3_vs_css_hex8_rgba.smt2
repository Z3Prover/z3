;; Category : CSS colors
;; Benchmark: css_hex3 vs css_hex8_rgba
;; R1: Short hex color: #[0-9a-fA-F]{3}
;; R2: RGBA hex with alpha: #[0-9a-fA-F]{8}
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
    (re.union (re.inter (re.++ (str.to_re "#") ((_ re.loop 3 3) (re.union (re.range "0" "9") (re.range "a" "f") (re.range "A" "F")))) (re.comp (re.++ (str.to_re "#") ((_ re.loop 8 8) (re.union (re.range "0" "9") (re.range "a" "f") (re.range "A" "F")))))) (re.inter (re.comp (re.++ (str.to_re "#") ((_ re.loop 3 3) (re.union (re.range "0" "9") (re.range "a" "f") (re.range "A" "F"))))) (re.++ (str.to_re "#") ((_ re.loop 8 8) (re.union (re.range "0" "9") (re.range "a" "f") (re.range "A" "F"))))))))

(check-sat)
(exit)
