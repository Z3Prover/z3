;; Category : Snort/DPI patterns
;; Benchmark: snort_http_get vs snort_http_with_host
;; R1: HTTP GET request line
;; R2: Request + Host header
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "snort")
(set-info :status sat)
(set-logic QF_S)

(declare-const x String)

(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "GET ") (str.to_re "/") (re.* (re.range "!" "~")) (str.to_re " HTTP/1.") (re.union (str.to_re "0") (str.to_re "1"))) (re.comp (re.++ (re.+ (re.range "A" "Z")) (str.to_re " ") (str.to_re "/") (re.* (re.range "!" "~")) (str.to_re " HTTP/1.") (re.union (str.to_re "0") (str.to_re "1")) (str.to_re "
Host: ") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "-")))))) (re.inter (re.comp (re.++ (str.to_re "GET ") (str.to_re "/") (re.* (re.range "!" "~")) (str.to_re " HTTP/1.") (re.union (str.to_re "0") (str.to_re "1")))) (re.++ (re.+ (re.range "A" "Z")) (str.to_re " ") (str.to_re "/") (re.* (re.range "!" "~")) (str.to_re " HTTP/1.") (re.union (str.to_re "0") (str.to_re "1")) (str.to_re "
Host: ") (re.+ (re.union (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")) (str.to_re ".") (str.to_re "-"))))))))

(check-sat)
(exit)
