;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance05751.smt2
;; Mutations:  literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_dec)
(assert
  (not
    (=
      (re.++ (re.union (re.++ (re.union (re.range "A" "P") (re.range "R" "U") (str.to_re "W") (str.to_re "Y") (str.to_re "Z") (re.range "0" "9")) (re.union (re.range "A" "H") (re.range "K" "Y") (re.range "0" "9")) (re.opt (re.union (str.to_re "A") (str.to_re "E") (str.to_re "H") (str.to_re "M") (str.to_re "N") (str.to_re "P") (str.to_re "R") (str.to_re "T") (str.to_re "V") (str.to_re "X") (str.to_re "Y") (re.range "0" "9"))) (re.opt (re.union (str.to_re "A") (str.to_re "B") (str.to_re "E") (str.to_re "H") (str.to_re "M") (str.to_re "N") (str.to_re "P") (str.to_re "R") (str.to_re "V") (str.to_re "W") (str.to_re "X") (str.to_re "Y") (re.range "0" "9"))) ((_ re.loop 1 2) (str.to_re " ")) (re.range "0" "9") ((_ re.loop 2 2) (re.union (str.to_re "A") (str.to_re "B") (re.range "D" "H") (str.to_re "J") (str.to_re "L") (re.range "N" "U") (re.range "W" "Z")))) (str.to_re "GIR 0AA")) (str.to_re "\u{a}"))
      (re.++ (re.union (re.++ (re.union (re.range "A" "P") (re.range "R" "U") (str.to_re "W") (str.to_re "Y") (str.to_re "Z") (re.range "0" "9")) (re.union (re.range "A" "H") (re.range "K" "Y") (re.range "0" "9")) (re.opt (re.union (str.to_re "A") (str.to_re "E") (str.to_re "H") (str.to_re "M") (str.to_re "M") (str.to_re "P") (str.to_re "R") (str.to_re "T") (str.to_re "V") (str.to_re "X") (str.to_re "Y") (re.range "0" "9"))) (re.opt (re.union (str.to_re "A") (str.to_re "B") (str.to_re "E") (str.to_re "H") (str.to_re "M") (str.to_re "N") (str.to_re "P") (str.to_re "R") (str.to_re "V") (str.to_re "W") (str.to_re "X") (str.to_re "Y") (re.range "0" "9"))) ((_ re.loop 1 2) (str.to_re " ")) (re.range "0" "9") ((_ re.loop 2 2) (re.union (str.to_re "A") (str.to_re "B") (re.range "D" "H") (str.to_re "J") (str.to_re "L") (re.range "N" "U") (re.range "W" "Z")))) (str.to_re "GIR 0AA")) (str.to_re "\u{a}")))))

(check-sat)
(exit)
