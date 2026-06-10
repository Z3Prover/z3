;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance03054.smt2
;; Mutations:  intersect_no_upper2, intersect_max_len_10, literal_char_dec
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
;; R2: mutated (intersect_no_upper2, intersect_max_len_10, literal_char_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "sips:") (re.opt (str.to_re "+")) (re.+ (re.union (str.to_re "|") (str.to_re ":") (str.to_re "?") (str.to_re ".") (str.to_re "-") (str.to_re "@") (str.to_re ";") (str.to_re ",") (str.to_re "=") (str.to_re "%") (str.to_re "&") (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "\u{a}")) (re.comp (re.++ (str.to_re "sips9") (re.inter (re.opt (str.to_re "+")) ((_ re.loop 0 10) re.allchar)) (re.inter (re.+ (re.union (str.to_re "|") (str.to_re ":") (str.to_re "?") (str.to_re ".") (str.to_re "-") (str.to_re "@") (str.to_re ";") (str.to_re ",") (str.to_re "=") (str.to_re "%") (str.to_re "&") (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "sips:") (re.opt (str.to_re "+")) (re.+ (re.union (str.to_re "|") (str.to_re ":") (str.to_re "?") (str.to_re ".") (str.to_re "-") (str.to_re "@") (str.to_re ";") (str.to_re ",") (str.to_re "=") (str.to_re "%") (str.to_re "&") (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "\u{a}"))) (re.++ (str.to_re "sips9") (re.inter (re.opt (str.to_re "+")) ((_ re.loop 0 10) re.allchar)) (re.inter (re.+ (re.union (str.to_re "|") (str.to_re ":") (str.to_re "?") (str.to_re ".") (str.to_re "-") (str.to_re "@") (str.to_re ";") (str.to_re ",") (str.to_re "=") (str.to_re "%") (str.to_re "&") (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
