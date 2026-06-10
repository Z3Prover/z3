;; Category : regexlib_equiv
;; Source   : RegExLib URL patterns
;; http+https vs http-only
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "regexlib_equiv")
(set-info :status sat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.++ (re.union (str.to_re "http://") (str.to_re "https://")) (re.++ (re.+ (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "-"))) (re.* (re.++ (str.to_re ".") (re.+ (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "-")))))) (re.* (re.++ (str.to_re "/") (re.* (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (re.union (str.to_re "-") (str.to_re "_") (str.to_re ".") (str.to_re "~"))))))) (re.comp (re.++ (str.to_re "http://") (re.++ (re.+ (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "-"))) (re.* (re.++ (str.to_re ".") (re.+ (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "-")))))) (re.* (re.++ (str.to_re "/") (re.* (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (re.union (str.to_re "-") (str.to_re "_") (str.to_re ".") (str.to_re "~")))))))))
      (re.inter (re.comp (re.++ (re.union (str.to_re "http://") (str.to_re "https://")) (re.++ (re.+ (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "-"))) (re.* (re.++ (str.to_re ".") (re.+ (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "-")))))) (re.* (re.++ (str.to_re "/") (re.* (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (re.union (str.to_re "-") (str.to_re "_") (str.to_re ".") (str.to_re "~")))))))) (re.++ (str.to_re "http://") (re.++ (re.+ (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "-"))) (re.* (re.++ (str.to_re ".") (re.+ (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "-")))))) (re.* (re.++ (str.to_re "/") (re.* (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (re.union (str.to_re "-") (str.to_re "_") (str.to_re ".") (str.to_re "~")))))))))))

(check-sat)
(exit)
