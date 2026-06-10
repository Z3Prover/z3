;; n = 16
;; Category : ba_ab_param
;; Source   : CAV'26 Table 1 -- p_n = (.*ba.*){n}, q_n = (.*ab.*){n} (inequivalent)
;; Demonstrates linear (bisim) vs quadratic (emptiness) state-space scaling.
;; Status   : sat   (R1 != R2; .*ba.* and .*ab.* differ as substrings)

(set-info :smt-lib-version 2.6)
(set-info :category "ba_ab_param")
(set-info :status sat)
(set-logic QF_S)

(assert (not (= ((_ re.loop 16 16) (re.++ (re.* re.allchar) (str.to_re "ba") (re.* re.allchar))) ((_ re.loop 16 16) (re.++ (re.* re.allchar) (str.to_re "ab") (re.* re.allchar))))))

(check-sat)
(exit)
