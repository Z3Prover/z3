;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance06240.smt2
;; Mutations:  literal_char_inc, intersect_min_len_5
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
;; R2: mutated (literal_char_inc, intersect_min_len_5)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "http://www") re.allchar (str.to_re "scribd") re.allchar (str.to_re "com/doc/2569355/Geo-Distance-Search-with-MySQL\u{a}")) (re.comp (re.++ (re.inter (str.to_re "http://www") (re.++ ((_ re.loop 5 5) re.allchar) re.all)) re.allchar (str.to_re "scribe") re.allchar (str.to_re "com/doc/2569355/Geo-Distance-Search-with-MySQL\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "http://www") re.allchar (str.to_re "scribd") re.allchar (str.to_re "com/doc/2569355/Geo-Distance-Search-with-MySQL\u{a}"))) (re.++ (re.inter (str.to_re "http://www") (re.++ ((_ re.loop 5 5) re.allchar) re.all)) re.allchar (str.to_re "scribe") re.allchar (str.to_re "com/doc/2569355/Geo-Distance-Search-with-MySQL\u{a}"))))))

(check-sat)
(exit)
