;; Category : Snort/DPI patterns
;; Benchmark: snort_http_any_method vs snort_http_with_host
;; R1: Any HTTP method: ALPHA+ /path HTTP/1.x
;; R2: Request + Host header
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "snort")
(set-info :status sat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.++ (re.+ (re.range "A" "Z")) (str.to_re " ") (str.to_re "/") (re.* (re.range "!" "~")) (str.to_re " HTTP/1.") (re.union (str.to_re "0") (str.to_re "1"))) (re.comp (re.++ (re.+ (re.range "A" "Z")) (str.to_re " ") (str.to_re "/") (re.* (re.range "!" "~")) (str.to_re " HTTP/1.") (re.union (str.to_re "0") (str.to_re "1")) (str.to_re "
Host: ") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "-"))))))
      (re.inter (re.comp (re.++ (re.+ (re.range "A" "Z")) (str.to_re " ") (str.to_re "/") (re.* (re.range "!" "~")) (str.to_re " HTTP/1.") (re.union (str.to_re "0") (str.to_re "1")))) (re.++ (re.+ (re.range "A" "Z")) (str.to_re " ") (str.to_re "/") (re.* (re.range "!" "~")) (str.to_re " HTTP/1.") (re.union (str.to_re "0") (str.to_re "1")) (str.to_re "
Host: ") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "-"))))))))

(check-sat)
(exit)
