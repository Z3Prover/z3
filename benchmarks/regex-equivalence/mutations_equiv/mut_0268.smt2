;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance02644.smt2
;; Mutations:  range_shrink_lo
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo)
(assert
  (not
    (=
      (re.++ (re.union (re.++ (re.opt (re.range "0" "1")) (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "3"))) (re.opt (re.++ (re.opt (str.to_re ":")) (re.range "0" "5") (re.range "0" "9"))) (re.opt (re.union (re.opt (str.to_re ":")) (re.++ (re.range "0" "5") (re.range "0" "9")))) (re.opt (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.opt (re.union (str.to_re "A") (str.to_re "AM") (str.to_re "P") (str.to_re "p") (str.to_re "a") (str.to_re "PM") (str.to_re "am") (str.to_re "pm") (str.to_re "pM") (str.to_re "aM") (str.to_re "Am") (str.to_re "Pm"))) (str.to_re "\u{a}"))
      (re.++ (re.union (re.++ (re.opt (re.range "0" "1")) (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "3"))) (re.opt (re.++ (re.opt (str.to_re ":")) (re.range "1" "5") (re.range "0" "9"))) (re.opt (re.union (re.opt (str.to_re ":")) (re.++ (re.range "0" "5") (re.range "0" "9")))) (re.opt (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.opt (re.union (str.to_re "A") (str.to_re "AM") (str.to_re "P") (str.to_re "p") (str.to_re "a") (str.to_re "PM") (str.to_re "am") (str.to_re "pm") (str.to_re "pM") (str.to_re "aM") (str.to_re "Am") (str.to_re "Pm"))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
