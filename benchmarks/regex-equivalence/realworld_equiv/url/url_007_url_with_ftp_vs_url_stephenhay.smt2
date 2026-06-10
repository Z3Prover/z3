;; Category : URL validation
;; Benchmark: url_with_ftp vs url_stephenhay
;; R1: Also allows FTP: (https?|ftp)://\S+
;; R2: Stephenhay-inspired: scheme://nonspecial.nonws*
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "url")
(set-info :status sat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.++ (re.union (re.++ (str.to_re "http") (re.opt (str.to_re "s"))) (str.to_re "ftp")) (str.to_re "://") (re.+ (re.range "!" "~"))) (re.comp (re.++ (re.union (re.++ (str.to_re "http") (re.opt (str.to_re "s"))) (str.to_re "ftp")) (str.to_re "://") (re.diff (re.range "!" "~") (re.union (str.to_re "/") (str.to_re "$") (str.to_re ".") (str.to_re "?") (str.to_re "#"))) (re.* (re.range "!" "~")))))
      (re.inter (re.comp (re.++ (re.union (re.++ (str.to_re "http") (re.opt (str.to_re "s"))) (str.to_re "ftp")) (str.to_re "://") (re.+ (re.range "!" "~")))) (re.++ (re.union (re.++ (str.to_re "http") (re.opt (str.to_re "s"))) (str.to_re "ftp")) (str.to_re "://") (re.diff (re.range "!" "~") (re.union (str.to_re "/") (str.to_re "$") (str.to_re ".") (str.to_re "?") (str.to_re "#"))) (re.* (re.range "!" "~")))))))

(check-sat)
(exit)
