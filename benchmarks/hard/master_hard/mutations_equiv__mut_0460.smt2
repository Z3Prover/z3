;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance13560.smt2
;; Mutations:  literal_char_dec, literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_dec, literal_char_inc)
(assert
  (not
    (=
      (re.++ (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c") (str.to_re "e") (str.to_re "g") (str.to_re "h") (str.to_re "j") (str.to_re "k") (str.to_re "l") (str.to_re "m") (str.to_re "n") (str.to_re "p") (str.to_re "r") (str.to_re "s") (str.to_re "t") (str.to_re "v") (str.to_re "x") (str.to_re "y") (str.to_re "A") (str.to_re "B") (str.to_re "C") (str.to_re "E") (str.to_re "G") (str.to_re "H") (str.to_re "J") (str.to_re "K") (str.to_re "L") (str.to_re "M") (str.to_re "N") (str.to_re "P") (str.to_re "R") (str.to_re "S") (str.to_re "T") (str.to_re "V") (str.to_re "X") (str.to_re "Y")) (re.range "0" "9") (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c") (str.to_re "e") (str.to_re "g") (str.to_re "h") (str.to_re "j") (str.to_re "k") (str.to_re "l") (str.to_re "m") (str.to_re "n") (str.to_re "p") (str.to_re "r") (str.to_re "s") (str.to_re "t") (str.to_re "v") (str.to_re "w") (str.to_re "x") (str.to_re "y") (str.to_re "z") (str.to_re "A") (str.to_re "B") (str.to_re "C") (str.to_re "E") (str.to_re "G") (str.to_re "H") (str.to_re "J") (str.to_re "K") (str.to_re "L") (str.to_re "M") (str.to_re "N") (str.to_re "P") (str.to_re "R") (str.to_re "S") (str.to_re "T") (str.to_re "V") (str.to_re "W") (str.to_re "X") (str.to_re "Y") (str.to_re "Z")) (re.opt (str.to_re " ")) (re.range "0" "9") (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c") (str.to_re "e") (str.to_re "g") (str.to_re "h") (str.to_re "j") (str.to_re "k") (str.to_re "l") (str.to_re "m") (str.to_re "n") (str.to_re "p") (str.to_re "r") (str.to_re "s") (str.to_re "t") (str.to_re "v") (str.to_re "w") (str.to_re "x") (str.to_re "y") (str.to_re "z") (str.to_re "A") (str.to_re "B") (str.to_re "C") (str.to_re "E") (str.to_re "G") (str.to_re "H") (str.to_re "J") (str.to_re "K") (str.to_re "L") (str.to_re "M") (str.to_re "N") (str.to_re "P") (str.to_re "R") (str.to_re "S") (str.to_re "T") (str.to_re "V") (str.to_re "W") (str.to_re "X") (str.to_re "Y") (str.to_re "Z")) (re.range "0" "9") (str.to_re "\u{a}"))
      (re.++ (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c") (str.to_re "e") (str.to_re "g") (str.to_re "h") (str.to_re "j") (str.to_re "k") (str.to_re "l") (str.to_re "m") (str.to_re "n") (str.to_re "p") (str.to_re "r") (str.to_re "s") (str.to_re "t") (str.to_re "v") (str.to_re "x") (str.to_re "y") (str.to_re "A") (str.to_re "B") (str.to_re "C") (str.to_re "E") (str.to_re "G") (str.to_re "H") (str.to_re "J") (str.to_re "K") (str.to_re "L") (str.to_re "M") (str.to_re "N") (str.to_re "P") (str.to_re "S") (str.to_re "S") (str.to_re "T") (str.to_re "V") (str.to_re "X") (str.to_re "Y")) (re.range "0" "9") (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c") (str.to_re "e") (str.to_re "g") (str.to_re "h") (str.to_re "j") (str.to_re "k") (str.to_re "l") (str.to_re "m") (str.to_re "n") (str.to_re "p") (str.to_re "r") (str.to_re "s") (str.to_re "t") (str.to_re "v") (str.to_re "w") (str.to_re "x") (str.to_re "y") (str.to_re "z") (str.to_re "@") (str.to_re "B") (str.to_re "C") (str.to_re "E") (str.to_re "G") (str.to_re "H") (str.to_re "J") (str.to_re "K") (str.to_re "L") (str.to_re "M") (str.to_re "N") (str.to_re "P") (str.to_re "R") (str.to_re "S") (str.to_re "T") (str.to_re "V") (str.to_re "W") (str.to_re "X") (str.to_re "Y") (str.to_re "Z")) (re.opt (str.to_re " ")) (re.range "0" "9") (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c") (str.to_re "e") (str.to_re "g") (str.to_re "h") (str.to_re "j") (str.to_re "k") (str.to_re "l") (str.to_re "m") (str.to_re "n") (str.to_re "p") (str.to_re "r") (str.to_re "s") (str.to_re "t") (str.to_re "v") (str.to_re "w") (str.to_re "x") (str.to_re "y") (str.to_re "z") (str.to_re "A") (str.to_re "B") (str.to_re "C") (str.to_re "E") (str.to_re "G") (str.to_re "H") (str.to_re "J") (str.to_re "K") (str.to_re "L") (str.to_re "M") (str.to_re "N") (str.to_re "P") (str.to_re "R") (str.to_re "S") (str.to_re "T") (str.to_re "V") (str.to_re "W") (str.to_re "X") (str.to_re "Y") (str.to_re "Z")) (re.range "0" "9") (str.to_re "\u{a}")))))

(check-sat)
(exit)
