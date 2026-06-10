;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance06115.smt2
;; Mutations:  literal_char_dec, literal_char_inc, intersect_no_at_sign
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_dec, literal_char_inc, intersect_no_at_sign)
(assert
  (not
    (=
      (re.++ (re.union (re.++ (re.union (re.++ (str.to_re "0") (re.union (str.to_re "1") (re.range "3" "7"))) (re.++ (str.to_re "1") (re.union (str.to_re "1") (str.to_re "2") (str.to_re "3") (str.to_re "5") (str.to_re "7") (str.to_re "8") (str.to_re "9"))) (re.++ (re.union (str.to_re "2") (str.to_re "5") (str.to_re "7")) (re.range "0" "9")) (re.++ (str.to_re "3") (re.union (re.range "0" "3") (re.range "5" "9"))) (re.++ (str.to_re "4") (re.union (str.to_re "0") (str.to_re "1") (str.to_re "2") (re.range "4" "9"))) (re.++ (str.to_re "6") (re.union (str.to_re "0") (str.to_re "1") (re.range "3" "7") (str.to_re "9"))) (re.++ (str.to_re "8") (re.union (str.to_re "0") (str.to_re "1") (str.to_re "2") (re.range "4" "9"))) (re.++ (str.to_re "9") (re.union (re.range "0" "5") (str.to_re "7") (str.to_re "8") (str.to_re "9")))) ((_ re.loop 3 3) (re.range "0" "9"))) (re.++ (str.to_re "10") (re.union (re.++ (re.range "2" "9") ((_ re.loop 2 2) (re.range "0" "9"))) (re.++ (str.to_re "1") (re.union (re.++ (re.range "2" "9") (re.range "0" "9")) (re.++ (str.to_re "11") (re.range "5" "9")))))) (re.++ (str.to_re "14") (re.union (re.++ (re.union (str.to_re "0") (str.to_re "1")) ((_ re.loop 2 2) (re.range "0" "9"))) (str.to_re "715")))) (str.to_re "\u{a}"))
      (re.++ (re.union (re.++ (re.union (re.inter (re.++ (str.to_re "0") (re.union (str.to_re "1") (re.range "3" "7"))) (re.comp (re.++ re.all (str.to_re "@") re.all))) (re.++ (str.to_re "1") (re.union (str.to_re "1") (str.to_re "2") (str.to_re "3") (str.to_re "5") (str.to_re "7") (str.to_re "8") (str.to_re "9"))) (re.++ (re.union (str.to_re "2") (str.to_re "5") (str.to_re "8")) (re.range "0" "9")) (re.++ (str.to_re "3") (re.union (re.range "0" "3") (re.range "5" "9"))) (re.++ (str.to_re "4") (re.union (str.to_re "0") (str.to_re "1") (str.to_re "2") (re.range "4" "9"))) (re.++ (str.to_re "6") (re.union (str.to_re "0") (str.to_re "1") (re.range "3" "7") (str.to_re "9"))) (re.++ (str.to_re "8") (re.union (str.to_re "0") (str.to_re "1") (str.to_re "2") (re.range "4" "9"))) (re.++ (str.to_re "9") (re.union (re.range "0" "5") (str.to_re "7") (str.to_re "8") (str.to_re "9")))) ((_ re.loop 3 3) (re.range "0" "9"))) (re.++ (str.to_re "10") (re.union (re.++ (re.range "2" "9") ((_ re.loop 2 2) (re.range "0" "9"))) (re.++ (str.to_re "1") (re.union (re.++ (re.range "2" "9") (re.range "0" "9")) (re.++ (str.to_re "11") (re.range "5" "9")))))) (re.++ (str.to_re "13") (re.union (re.++ (re.union (str.to_re "0") (str.to_re "1")) ((_ re.loop 2 2) (re.range "0" "9"))) (str.to_re "715")))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
