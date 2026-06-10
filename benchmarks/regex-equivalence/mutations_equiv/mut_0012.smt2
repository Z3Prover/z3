;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance01860.smt2
;; Mutations:  literal_char_inc, intersect_min_len_5
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_inc, intersect_min_len_5)
(assert
  (not
    (=
      (re.++ (str.to_re "/") (re.union (str.to_re "www.") (str.to_re "http://") (str.to_re "https://") (str.to_re "http://www.") (str.to_re "https://www.")) (re.+ (re.union (re.range "a" "z") (re.range "0" "9"))) (str.to_re ".") ((_ re.loop 2 4) (re.range "a" "z")) (str.to_re "/\u{a}"))
      (re.++ (str.to_re "/") (re.union (str.to_re "www.") (re.inter (str.to_re "http://") (re.++ ((_ re.loop 5 5) re.allchar) re.all)) (str.to_re "https://") (str.to_re "http://www/") (str.to_re "https://www.")) (re.+ (re.union (re.range "a" "z") (re.range "0" "9"))) (str.to_re ".") ((_ re.loop 2 4) (re.range "a" "z")) (str.to_re "/\u{a}")))))

(check-sat)
(exit)
