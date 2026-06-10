;; Category : CSS colors
;; Benchmark: css_hex3 vs css_hex6_lower
;; R1: Short hex color: #[0-9a-fA-F]{3}
;; R2: Lowercase-only hex: #[0-9a-f]{6}
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "css")
(set-info :status sat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.++ (str.to_re "#") ((_ re.loop 3 3) (re.union (re.range "0" "9") (re.range "a" "f") (re.range "A" "F")))) (re.comp (re.++ (str.to_re "#") ((_ re.loop 6 6) (re.union (re.range "0" "9") (re.range "a" "f"))))))
      (re.inter (re.comp (re.++ (str.to_re "#") ((_ re.loop 3 3) (re.union (re.range "0" "9") (re.range "a" "f") (re.range "A" "F"))))) (re.++ (str.to_re "#") ((_ re.loop 6 6) (re.union (re.range "0" "9") (re.range "a" "f"))))))))

(check-sat)
(exit)
