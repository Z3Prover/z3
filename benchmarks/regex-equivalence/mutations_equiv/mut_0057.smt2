;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11926.smt2
;; Mutations:  literal_char_inc, bound_upper_dec, literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_inc, bound_upper_dec, literal_char_inc)
(assert
  (not
    (=
      (re.++ (re.* (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.opt (str.to_re "-")) (re.union ((_ re.loop 0 7) (re.range "0" "9")) (re.++ (str.to_re "10") (re.range "0" "5") ((_ re.loop 0 5) (re.range "0" "9"))) (re.++ (str.to_re "106") (re.range "0" "6") ((_ re.loop 0 4) (re.range "0" "9"))) (re.++ (str.to_re "1067") (re.range "0" "4") ((_ re.loop 0 3) (re.range "0" "9"))) (re.++ (str.to_re "10675") (re.range "0" "1") ((_ re.loop 0 2) (re.range "0" "9"))) (re.++ (re.opt (re.++ (re.union ((_ re.loop 0 7) (re.range "0" "9")) (re.++ (str.to_re "10") (re.range "0" "5") ((_ re.loop 0 5) (re.range "0" "9"))) (re.++ (str.to_re "106") (re.range "0" "6") ((_ re.loop 0 4) (re.range "0" "9"))) (re.++ (str.to_re "1067") (re.range "0" "4") ((_ re.loop 0 3) (re.range "0" "9"))) (re.++ (str.to_re "10675") (re.range "0" "1") ((_ re.loop 0 2) (re.range "0" "9")))) (str.to_re "."))) (re.union (re.++ (re.opt (re.range "0" "1")) (re.range "0" "9")) (re.++ (str.to_re "2") (re.range "0" "3"))) (str.to_re ":") (re.opt (re.range "0" "5")) (re.range "0" "9") (re.opt (re.++ (str.to_re ":") (re.opt (re.range "0" "5")) (re.range "0" "9") (re.opt (re.++ (str.to_re ".") ((_ re.loop 1 7) (re.range "0" "9")))))))) (re.* (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "\u{a}"))
      (re.++ (re.* (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.opt (str.to_re "-")) (re.union ((_ re.loop 0 7) (re.range "0" "9")) (re.++ (str.to_re "10") (re.range "0" "5") ((_ re.loop 0 5) (re.range "0" "9"))) (re.++ (str.to_re "106") (re.range "0" "6") ((_ re.loop 0 4) (re.range "0" "9"))) (re.++ (str.to_re "1067") (re.range "0" "4") ((_ re.loop 0 3) (re.range "0" "9"))) (re.++ (str.to_re "10675") (re.range "0" "1") ((_ re.loop 0 2) (re.range "0" "9"))) (re.++ (re.opt (re.++ (re.union ((_ re.loop 0 7) (re.range "0" "9")) (re.++ (str.to_re "10") (re.range "0" "5") ((_ re.loop 0 5) (re.range "0" "9"))) (re.++ (str.to_re "107") (re.range "0" "6") ((_ re.loop 0 3) (re.range "0" "9"))) (re.++ (str.to_re "1067") (re.range "0" "4") ((_ re.loop 0 3) (re.range "0" "9"))) (re.++ (str.to_re "10675") (re.range "0" "1") ((_ re.loop 0 2) (re.range "0" "9")))) (str.to_re "."))) (re.union (re.++ (re.opt (re.range "0" "1")) (re.range "0" "9")) (re.++ (str.to_re "3") (re.range "0" "3"))) (str.to_re ":") (re.opt (re.range "0" "5")) (re.range "0" "9") (re.opt (re.++ (str.to_re ":") (re.opt (re.range "0" "5")) (re.range "0" "9") (re.opt (re.++ (str.to_re ".") ((_ re.loop 1 7) (re.range "0" "9")))))))) (re.* (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
