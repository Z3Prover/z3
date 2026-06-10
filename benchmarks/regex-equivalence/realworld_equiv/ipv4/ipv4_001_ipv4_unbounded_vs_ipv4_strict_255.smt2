;; Category : IPv4 addresses
;; Benchmark: ipv4_unbounded vs ipv4_strict_255
;; R1: Unbounded digits: d+.d+.d+.d+
;; R2: Strict 0-255 per octet, no leading zeros
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "ipv4")
(set-info :status sat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.++ (re.+ (re.range "0" "9")) (str.to_re ".") (re.+ (re.range "0" "9")) (str.to_re ".") (re.+ (re.range "0" "9")) (str.to_re ".") (re.+ (re.range "0" "9"))) (re.comp (re.++ (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5"))) (str.to_re ".") (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5"))) (str.to_re ".") (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5"))) (str.to_re ".") (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5"))))))
      (re.inter (re.comp (re.++ (re.+ (re.range "0" "9")) (str.to_re ".") (re.+ (re.range "0" "9")) (str.to_re ".") (re.+ (re.range "0" "9")) (str.to_re ".") (re.+ (re.range "0" "9")))) (re.++ (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5"))) (str.to_re ".") (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5"))) (str.to_re ".") (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5"))) (str.to_re ".") (re.union (str.to_re "0") (re.++ (re.range "1" "9") (re.opt (re.range "0" "9"))) (re.++ (str.to_re "1") (re.range "0" "9") (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "4") (re.range "0" "9")) (re.++ (str.to_re "2") (str.to_re "5") (re.range "0" "5"))))))))

(check-sat)
(exit)
