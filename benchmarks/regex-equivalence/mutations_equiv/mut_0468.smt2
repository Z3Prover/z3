;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance13208.smt2
;; Mutations:  union_to_inter, plus_to_star, literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (union_to_inter, plus_to_star, literal_char_inc)
(assert
  (not
    (=
      (re.++ (str.to_re "eveocczmthmmq/omzl") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "zmnjgmomgbdz/zzmw.gzt\u{a}"))
      (re.++ (str.to_re "eveocczmthmmq/omzm") (re.* (re.inter (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "zmnjgmomgbdz/zzmw.gzt\u{a}")))))

(check-sat)
(exit)
