;; Category : parametric
;; Source   : Constructed (XOR primitive test)
;; R△R ≡ ∅ (self-inverse), n=20
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "parametric")
(set-info :status unsat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.union (re.inter ((_ re.loop 20 20) (re.++ (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a"))) (re.comp ((_ re.loop 20 20) (re.++ (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a"))))) (re.inter (re.comp ((_ re.loop 20 20) (re.++ (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a")))) ((_ re.loop 20 20) (re.++ (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a"))))) (re.comp re.none))
      (re.inter (re.comp (re.union (re.inter ((_ re.loop 20 20) (re.++ (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a"))) (re.comp ((_ re.loop 20 20) (re.++ (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a"))))) (re.inter (re.comp ((_ re.loop 20 20) (re.++ (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a")))) ((_ re.loop 20 20) (re.++ (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a")))))) re.none))))

(check-sat)
(exit)
