;; Category : Snort/DPI patterns
;; Benchmark: snort_http_get vs snort_http_any_method
;; R1: HTTP GET request line
;; R2: Any HTTP method: ALPHA+ /path HTTP/1.x
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
      (re.inter (re.++ (str.to_re "GET ") (str.to_re "/") (re.* (re.range "!" "~")) (str.to_re " HTTP/1.") (re.union (str.to_re "0") (str.to_re "1"))) (re.comp (re.++ (re.+ (re.range "A" "Z")) (str.to_re " ") (str.to_re "/") (re.* (re.range "!" "~")) (str.to_re " HTTP/1.") (re.union (str.to_re "0") (str.to_re "1")))))
      (re.inter (re.comp (re.++ (str.to_re "GET ") (str.to_re "/") (re.* (re.range "!" "~")) (str.to_re " HTTP/1.") (re.union (str.to_re "0") (str.to_re "1")))) (re.++ (re.+ (re.range "A" "Z")) (str.to_re " ") (str.to_re "/") (re.* (re.range "!" "~")) (str.to_re " HTTP/1.") (re.union (str.to_re "0") (str.to_re "1")))))))

(check-sat)
(exit)
