;; Category : URL validation
;; Benchmark: url_stephenhay vs url_domain_userinfo
;; R1: Stephenhay-inspired: scheme://nonspecial.nonws*
;; R2: Optional userinfo@ + domain + port + path
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "url")
(set-info :status sat)
(set-logic QF_S)

(declare-const x String)

(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.union (re.++ (str.to_re "http") (re.opt (str.to_re "s"))) (str.to_re "ftp")) (str.to_re "://") (re.diff (re.range "!" "~") (re.union (str.to_re "/") (str.to_re "$") (str.to_re ".") (str.to_re "?") (str.to_re "#"))) (re.* (re.range "!" "~"))) (re.comp (re.++ (str.to_re "http") (re.opt (str.to_re "s")) (str.to_re "://") (re.opt (re.++ (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "-") (str.to_re "_") (str.to_re "~"))) (re.opt (re.++ (str.to_re ":") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "-") (str.to_re "_") (str.to_re "~"))))) (str.to_re "@"))) (re.++ (re.++ (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (re.opt (re.++ (re.* (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re "-"))) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))))) (re.* (re.++ (str.to_re ".") (re.++ (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (re.opt (re.++ (re.* (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re "-"))) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")))))))) (re.opt (re.++ (str.to_re ":") ((_ re.loop 1 5) (re.range "0" "9")))) (re.opt (re.++ (str.to_re "/") (re.* (re.range "!" "~"))))))) (re.inter (re.comp (re.++ (re.union (re.++ (str.to_re "http") (re.opt (str.to_re "s"))) (str.to_re "ftp")) (str.to_re "://") (re.diff (re.range "!" "~") (re.union (str.to_re "/") (str.to_re "$") (str.to_re ".") (str.to_re "?") (str.to_re "#"))) (re.* (re.range "!" "~")))) (re.++ (str.to_re "http") (re.opt (str.to_re "s")) (str.to_re "://") (re.opt (re.++ (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "-") (str.to_re "_") (str.to_re "~"))) (re.opt (re.++ (str.to_re ":") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "-") (str.to_re "_") (str.to_re "~"))))) (str.to_re "@"))) (re.++ (re.++ (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (re.opt (re.++ (re.* (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re "-"))) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))))) (re.* (re.++ (str.to_re ".") (re.++ (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (re.opt (re.++ (re.* (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re "-"))) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")))))))) (re.opt (re.++ (str.to_re ":") ((_ re.loop 1 5) (re.range "0" "9")))) (re.opt (re.++ (str.to_re "/") (re.* (re.range "!" "~")))))))))

(check-sat)
(exit)
