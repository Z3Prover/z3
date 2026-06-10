;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance13670.smt2
;; Mutations:  intersect_min_len_5, literal_char_dec, literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_min_len_5, literal_char_dec, literal_char_inc)
(assert
  (not
    (=
      (re.++ (re.union (re.++ (str.to_re "A") (re.union (str.to_re "L") (str.to_re "K") (str.to_re "Z") (str.to_re "R"))) (re.++ (str.to_re "C") (re.union (str.to_re "A") (str.to_re "O") (str.to_re "T"))) (re.++ (str.to_re "D") (re.union (str.to_re "E") (str.to_re "C"))) (str.to_re "FL") (str.to_re "GA") (str.to_re "HI") (re.++ (str.to_re "I") (re.union (str.to_re "D") (str.to_re "L") (str.to_re "N") (str.to_re "A"))) (re.++ (str.to_re "K") (re.union (str.to_re "S") (str.to_re "Y"))) (str.to_re "LA") (re.++ (str.to_re "M") (re.union (str.to_re "E") (str.to_re "D") (str.to_re "A") (str.to_re "I") (str.to_re "N") (str.to_re "S") (str.to_re "O") (str.to_re "T"))) (re.++ (str.to_re "N") (re.union (str.to_re "E") (str.to_re "V") (str.to_re "H") (str.to_re "J") (str.to_re "M") (str.to_re "Y") (str.to_re "C") (str.to_re "D"))) (re.++ (str.to_re "O") (re.union (str.to_re "H") (str.to_re "K") (str.to_re "R"))) (str.to_re "PA") (str.to_re "RI") (re.++ (str.to_re "S") (re.union (str.to_re "C") (str.to_re "D"))) (re.++ (str.to_re "T") (re.union (str.to_re "N") (str.to_re "X"))) (str.to_re "UT") (re.++ (str.to_re "V") (re.union (str.to_re "T") (str.to_re "A"))) (re.++ (str.to_re "W") (re.union (str.to_re "A") (str.to_re "V") (str.to_re "I") (str.to_re "Y")))) (str.to_re "\u{a}"))
      (re.++ (re.union (re.++ (str.to_re "B") (re.union (str.to_re "L") (str.to_re "K") (str.to_re "Z") (str.to_re "R"))) (re.++ (str.to_re "C") (re.union (str.to_re "A") (str.to_re "O") (str.to_re "T"))) (re.++ (str.to_re "D") (re.union (str.to_re "E") (str.to_re "C"))) (str.to_re "FL") (str.to_re "GA") (str.to_re "HI") (re.++ (str.to_re "I") (re.union (str.to_re "D") (str.to_re "L") (str.to_re "N") (str.to_re "A"))) (re.++ (str.to_re "K") (re.union (str.to_re "S") (str.to_re "Y"))) (str.to_re "LA") (re.++ (str.to_re "M") (re.union (str.to_re "E") (str.to_re "D") (str.to_re "A") (str.to_re "I") (str.to_re "N") (str.to_re "S") (str.to_re "O") (str.to_re "T"))) (re.++ (str.to_re "N") (re.union (str.to_re "E") (str.to_re "V") (str.to_re "H") (str.to_re "J") (str.to_re "M") (str.to_re "X") (str.to_re "C") (str.to_re "D"))) (re.++ (str.to_re "O") (re.union (str.to_re "H") (str.to_re "K") (str.to_re "R"))) (str.to_re "PA") (str.to_re "RI") (re.inter (re.++ (str.to_re "S") (re.union (str.to_re "C") (str.to_re "D"))) (re.++ ((_ re.loop 5 5) re.allchar) re.all)) (re.++ (str.to_re "T") (re.union (str.to_re "N") (str.to_re "X"))) (str.to_re "UT") (re.++ (str.to_re "V") (re.union (str.to_re "T") (str.to_re "A"))) (re.++ (str.to_re "W") (re.union (str.to_re "A") (str.to_re "V") (str.to_re "I") (str.to_re "Y")))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
