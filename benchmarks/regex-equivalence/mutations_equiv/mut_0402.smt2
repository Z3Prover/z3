;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11212.smt2
;; Mutations:  union_to_inter, literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (union_to_inter, literal_char_dec)
(assert
  (not
    (=
      (re.++ (re.opt (re.++ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.union (re.range "1" "9") (re.++ (str.to_re "1") (re.union (str.to_re "0") (str.to_re "2")))) (str.to_re ":") (re.union (re.++ (str.to_re ":") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.range "0" "5") (re.range "0" "9")) (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) ((_ re.loop 2 2) (re.union (str.to_re "A") (str.to_re "M") (str.to_re "|") (str.to_re "P") (str.to_re "a") (str.to_re "m") (str.to_re "p"))) (re.range "0" "5") (re.range "0" "9"))) (str.to_re "\u{a}") (re.union (re.++ (re.union (re.++ (str.to_re "1") (re.range "0" "2")) (str.to_re "1") (str.to_re "3") (str.to_re "5") (str.to_re "7") (str.to_re "8")) (re.opt (re.union (str.to_re "-") (str.to_re "/") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.union (re.range "1" "9") (re.++ (re.range "1" "2") (re.range "0" "9")) (re.++ (str.to_re "3") (re.union (str.to_re "0") (str.to_re "1"))))) (re.++ (re.union (str.to_re "11") (str.to_re "4") (str.to_re "6") (str.to_re "9")) (re.opt (re.union (str.to_re "-") (str.to_re "/") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.union (re.range "1" "9") (re.++ (re.range "1" "2") (re.range "0" "9")) (str.to_re "30"))) (re.++ (str.to_re "2") (re.opt (re.union (str.to_re "-") (str.to_re "/") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.union (re.range "1" "9") (re.++ (re.range "1" "2") (re.range "0" "9"))))) (re.opt (re.union (str.to_re "-") (str.to_re "/") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) ((_ re.loop 4 4) (re.range "0" "9")))
      (re.++ (re.opt (re.++ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.union (re.range "1" "9") (re.++ (str.to_re "1") (re.union (str.to_re "0") (str.to_re "2")))) (str.to_re ":") (re.union (re.++ (str.to_re "9") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.range "0" "5") (re.range "0" "9")) (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) ((_ re.loop 2 2) (re.union (str.to_re "A") (str.to_re "M") (str.to_re "|") (str.to_re "P") (str.to_re "a") (str.to_re "m") (str.to_re "p"))) (re.range "0" "5") (re.range "0" "9"))) (str.to_re "\u{a}") (re.inter (re.++ (re.union (re.++ (str.to_re "1") (re.range "0" "2")) (str.to_re "1") (str.to_re "3") (str.to_re "5") (str.to_re "7") (str.to_re "8")) (re.opt (re.union (str.to_re "-") (str.to_re "/") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.union (re.range "1" "9") (re.++ (re.range "1" "2") (re.range "0" "9")) (re.++ (str.to_re "3") (re.union (str.to_re "0") (str.to_re "1"))))) (re.++ (re.union (str.to_re "11") (str.to_re "4") (str.to_re "6") (str.to_re "9")) (re.opt (re.union (str.to_re "-") (str.to_re "/") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.union (re.range "1" "9") (re.++ (re.range "1" "2") (re.range "0" "9")) (str.to_re "30"))) (re.++ (str.to_re "2") (re.opt (re.union (str.to_re "-") (str.to_re "/") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.union (re.range "1" "9") (re.++ (re.range "1" "2") (re.range "0" "9"))))) (re.opt (re.union (str.to_re "-") (str.to_re "/") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) ((_ re.loop 4 4) (re.range "0" "9"))))))

(check-sat)
(exit)
