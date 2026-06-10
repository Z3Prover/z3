;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance05204.smt2
;; Mutations:  intersect_no_spaces, literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)

(declare-const x String)

;; R1: original
;; R2: mutated (intersect_no_spaces, literal_char_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "is") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "gdvsotuqwsg/dxt.hd\u{a}")) (re.comp (re.++ (str.to_re "ir") (re.+ (re.inter (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_")) (re.comp (re.++ re.all (str.to_re " ") re.all)))) (str.to_re "gdvsotuqwsg/dxt.hd\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "is") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "gdvsotuqwsg/dxt.hd\u{a}"))) (re.++ (str.to_re "ir") (re.+ (re.inter (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_")) (re.comp (re.++ re.all (str.to_re " ") re.all)))) (str.to_re "gdvsotuqwsg/dxt.hd\u{a}"))))))

(check-sat)
(exit)
