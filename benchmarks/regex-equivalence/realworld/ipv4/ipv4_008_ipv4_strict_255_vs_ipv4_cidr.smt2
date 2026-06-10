;; Category : IPv4 addresses
;; Benchmark: ipv4_strict_255 vs ipv4_cidr
;; R1: Strict 0-255 per octet, no leading zeros
;; R2: Bounded + optional /prefix-length
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "ipv4")
(set-info :status sat)
(set-logic QF_S)

(declare-const x String)

(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5"))) (str.to_re ".") (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5"))) (str.to_re ".") (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5"))) (str.to_re ".") (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5")))) (re.comp (re.++ (re.++ ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 1 3) (re.range "0" "9"))) (re.opt (re.++ (str.to_re "/") ((_ re.loop 1 2) (re.range "0" "9"))))))) (re.inter (re.comp (re.++ (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5"))) (str.to_re ".") (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5"))) (str.to_re ".") (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5"))) (str.to_re ".") (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5"))))) (re.++ (re.++ ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 1 3) (re.range "0" "9")) (str.to_re ".") ((_ re.loop 1 3) (re.range "0" "9"))) (re.opt (re.++ (str.to_re "/") ((_ re.loop 1 2) (re.range "0" "9")))))))))

(check-sat)
(exit)
