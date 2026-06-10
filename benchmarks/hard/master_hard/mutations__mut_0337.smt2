;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance14902.smt2
;; Mutations:  literal_char_inc, literal_char_dec
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
;; R2: mutated (literal_char_inc, literal_char_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "{") ((_ re.loop 8 8) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "A" "F") (re.range "a" "f") (str.to_re "0") (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 12 12) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re "}\u{a}")) (re.comp (re.++ (str.to_re "{") ((_ re.loop 8 8) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re ",") ((_ re.loop 4 4) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "A" "F") (re.range "a" "f") (str.to_re "1") (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 12 12) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re "}\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "{") ((_ re.loop 8 8) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "A" "F") (re.range "a" "f") (str.to_re "0") (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 12 12) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re "}\u{a}"))) (re.++ (str.to_re "{") ((_ re.loop 8 8) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re ",") ((_ re.loop 4 4) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "A" "F") (re.range "a" "f") (str.to_re "1") (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 4 4) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 12 12) (re.union (re.range "A" "F") (re.range "a" "f") (re.range "0" "9"))) (str.to_re "}\u{a}"))))))

(check-sat)
(exit)
