;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance05199.smt2
;; Mutations:  intersect_max_len_20, range_shrink_hi
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
;; R2: mutated (intersect_max_len_20, range_shrink_hi)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "/stop|") (re.+ (re.range "0" "9")) (str.to_re "|") (re.+ (re.range "0" "9")) (str.to_re "|") (re.+ (re.union (re.range "a" "z") (re.range "0" "9"))) (str.to_re ".") ((_ re.loop 2 3) (re.range "a" "z")) (str.to_re "|") (re.+ (re.union (re.range "a" "z") (re.range "0" "9"))) (str.to_re "|/\u{a}")) (re.comp (re.++ (str.to_re "/stop|") (re.+ (re.range "0" "9")) (str.to_re "|") (re.+ (re.range "0" "8")) (str.to_re "|") (re.+ (re.union (re.range "a" "z") (re.range "0" "9"))) (str.to_re ".") ((_ re.loop 2 3) (re.range "a" "z")) (str.to_re "|") (re.+ (re.inter (re.union (re.range "a" "z") (re.range "0" "9")) ((_ re.loop 0 20) re.allchar))) (str.to_re "|/\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "/stop|") (re.+ (re.range "0" "9")) (str.to_re "|") (re.+ (re.range "0" "9")) (str.to_re "|") (re.+ (re.union (re.range "a" "z") (re.range "0" "9"))) (str.to_re ".") ((_ re.loop 2 3) (re.range "a" "z")) (str.to_re "|") (re.+ (re.union (re.range "a" "z") (re.range "0" "9"))) (str.to_re "|/\u{a}"))) (re.++ (str.to_re "/stop|") (re.+ (re.range "0" "9")) (str.to_re "|") (re.+ (re.range "0" "8")) (str.to_re "|") (re.+ (re.union (re.range "a" "z") (re.range "0" "9"))) (str.to_re ".") ((_ re.loop 2 3) (re.range "a" "z")) (str.to_re "|") (re.+ (re.inter (re.union (re.range "a" "z") (re.range "0" "9")) ((_ re.loop 0 20) re.allchar))) (str.to_re "|/\u{a}"))))))

(check-sat)
(exit)
