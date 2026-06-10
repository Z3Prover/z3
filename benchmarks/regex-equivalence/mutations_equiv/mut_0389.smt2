;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance13011.smt2
;; Mutations:  literal_char_inc, literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_inc, literal_char_dec)
(assert
  (not
    (=
      (re.++ (re.union (re.++ (str.to_re "B") (re.union (str.to_re "A") (str.to_re "B") (str.to_re "C") (str.to_re "J") (str.to_re "L") (str.to_re "N") (str.to_re "R") (str.to_re "S") (str.to_re "Y"))) (str.to_re "CA") (re.++ (str.to_re "D") (re.union (str.to_re "K") (str.to_re "S") (str.to_re "T"))) (re.++ (str.to_re "G") (re.union (str.to_re "A") (str.to_re "L"))) (re.++ (str.to_re "H") (re.union (str.to_re "C") (str.to_re "E"))) (str.to_re "IL") (re.++ (str.to_re "K") (re.union (str.to_re "A") (str.to_re "I") (str.to_re "E") (str.to_re "K") (str.to_re "M") (str.to_re "N") (str.to_re "S"))) (re.++ (str.to_re "L") (re.union (str.to_re "E") (str.to_re "C") (str.to_re "M") (str.to_re "V"))) (re.++ (str.to_re "M") (re.union (str.to_re "A") (str.to_re "I") (str.to_re "L") (str.to_re "T") (str.to_re "Y"))) (re.++ (str.to_re "N") (re.union (str.to_re "I") (str.to_re "O") (str.to_re "M") (str.to_re "R") (str.to_re "Z"))) (re.++ (str.to_re "P") (re.union (str.to_re "B") (str.to_re "D") (str.to_re "E") (str.to_re "O") (str.to_re "K") (str.to_re "N") (str.to_re "P") (str.to_re "T") (str.to_re "U") (str.to_re "V"))) (re.++ (str.to_re "R") (re.union (str.to_re "A") (str.to_re "K") (str.to_re "S") (str.to_re "V"))) (re.++ (str.to_re "S") (re.union (str.to_re "A") (str.to_re "B") (str.to_re "C") (str.to_re "E") (str.to_re "I") (str.to_re "K") (str.to_re "L") (str.to_re "O") (str.to_re "N") (str.to_re "P") (str.to_re "V"))) (re.++ (str.to_re "T") (re.union (str.to_re "A") (str.to_re "C") (str.to_re "N") (str.to_re "O") (str.to_re "R") (str.to_re "S") (str.to_re "T") (str.to_re "V"))) (re.++ (str.to_re "V") (re.union (str.to_re "K") (str.to_re "T"))) (re.++ (str.to_re "Z") (re.union (str.to_re "A") (str.to_re "C") (str.to_re "H") (str.to_re "I") (str.to_re "M") (str.to_re "V")))) (re.opt (str.to_re " ")) ((_ re.loop 3 3) (re.range "0" "9")) ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "\u{a}"))
      (re.++ (re.union (re.++ (str.to_re "B") (re.union (str.to_re "A") (str.to_re "B") (str.to_re "C") (str.to_re "J") (str.to_re "L") (str.to_re "N") (str.to_re "R") (str.to_re "R") (str.to_re "Y"))) (str.to_re "CA") (re.++ (str.to_re "D") (re.union (str.to_re "K") (str.to_re "S") (str.to_re "T"))) (re.++ (str.to_re "G") (re.union (str.to_re "A") (str.to_re "L"))) (re.++ (str.to_re "H") (re.union (str.to_re "C") (str.to_re "E"))) (str.to_re "IL") (re.++ (str.to_re "K") (re.union (str.to_re "A") (str.to_re "I") (str.to_re "E") (str.to_re "K") (str.to_re "M") (str.to_re "N") (str.to_re "S"))) (re.++ (str.to_re "L") (re.union (str.to_re "E") (str.to_re "C") (str.to_re "M") (str.to_re "V"))) (re.++ (str.to_re "M") (re.union (str.to_re "A") (str.to_re "I") (str.to_re "L") (str.to_re "T") (str.to_re "Z"))) (re.++ (str.to_re "N") (re.union (str.to_re "I") (str.to_re "O") (str.to_re "M") (str.to_re "R") (str.to_re "Z"))) (re.++ (str.to_re "P") (re.union (str.to_re "B") (str.to_re "D") (str.to_re "E") (str.to_re "O") (str.to_re "K") (str.to_re "N") (str.to_re "P") (str.to_re "T") (str.to_re "U") (str.to_re "V"))) (re.++ (str.to_re "R") (re.union (str.to_re "A") (str.to_re "K") (str.to_re "S") (str.to_re "V"))) (re.++ (str.to_re "S") (re.union (str.to_re "A") (str.to_re "B") (str.to_re "C") (str.to_re "E") (str.to_re "I") (str.to_re "K") (str.to_re "L") (str.to_re "O") (str.to_re "N") (str.to_re "P") (str.to_re "V"))) (re.++ (str.to_re "T") (re.union (str.to_re "A") (str.to_re "C") (str.to_re "N") (str.to_re "O") (str.to_re "R") (str.to_re "S") (str.to_re "T") (str.to_re "V"))) (re.++ (str.to_re "V") (re.union (str.to_re "K") (str.to_re "T"))) (re.++ (str.to_re "Z") (re.union (str.to_re "A") (str.to_re "C") (str.to_re "H") (str.to_re "I") (str.to_re "M") (str.to_re "V")))) (re.opt (str.to_re " ")) ((_ re.loop 3 3) (re.range "0" "9")) ((_ re.loop 2 2) (re.range "A" "Z")) (str.to_re "\u{a}")))))

(check-sat)
(exit)
