;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11893.smt2
;; Mutations:  range_shrink_hi, literal_char_inc
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
;; R2: mutated (range_shrink_hi, literal_char_inc)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ ((_ re.loop 5 5) (re.union (re.range "A" "Z") (re.range "0" "9"))) (re.range "0" "9") (re.union (str.to_re "0") (str.to_re "1") (str.to_re "5") (str.to_re "6")) (re.range "0" "9") (re.union (re.++ (str.to_re "0") (re.range "1" "9")) (re.++ (re.union (str.to_re "1") (str.to_re "2")) (re.range "0" "9")) (re.++ (str.to_re "3") (re.union (str.to_re "0") (str.to_re "1")))) (re.range "0" "9") ((_ re.loop 3 3) (re.union (re.range "A" "Z") (re.range "0" "9"))) ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "\u{a}")) (re.comp (re.++ ((_ re.loop 5 5) (re.union (re.range "A" "Z") (re.range "0" "9"))) (re.range "0" "9") (re.union (str.to_re "0") (str.to_re "1") (str.to_re "5") (str.to_re "7")) (re.range "0" "9") (re.union (re.++ (str.to_re "0") (re.range "1" "8")) (re.++ (re.union (str.to_re "1") (str.to_re "2")) (re.range "0" "9")) (re.++ (str.to_re "3") (re.union (str.to_re "0") (str.to_re "1")))) (re.range "0" "9") ((_ re.loop 3 3) (re.union (re.range "A" "Z") (re.range "0" "9"))) ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ ((_ re.loop 5 5) (re.union (re.range "A" "Z") (re.range "0" "9"))) (re.range "0" "9") (re.union (str.to_re "0") (str.to_re "1") (str.to_re "5") (str.to_re "6")) (re.range "0" "9") (re.union (re.++ (str.to_re "0") (re.range "1" "9")) (re.++ (re.union (str.to_re "1") (str.to_re "2")) (re.range "0" "9")) (re.++ (str.to_re "3") (re.union (str.to_re "0") (str.to_re "1")))) (re.range "0" "9") ((_ re.loop 3 3) (re.union (re.range "A" "Z") (re.range "0" "9"))) ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "\u{a}"))) (re.++ ((_ re.loop 5 5) (re.union (re.range "A" "Z") (re.range "0" "9"))) (re.range "0" "9") (re.union (str.to_re "0") (str.to_re "1") (str.to_re "5") (str.to_re "7")) (re.range "0" "9") (re.union (re.++ (str.to_re "0") (re.range "1" "8")) (re.++ (re.union (str.to_re "1") (str.to_re "2")) (re.range "0" "9")) (re.++ (str.to_re "3") (re.union (str.to_re "0") (str.to_re "1")))) (re.range "0" "9") ((_ re.loop 3 3) (re.union (re.range "A" "Z") (re.range "0" "9"))) ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
