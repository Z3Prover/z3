;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11843.smt2
;; Mutations:  intersect_min_len_5, intersect_no_digits4, literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_min_len_5, intersect_no_digits4, literal_char_inc)
(assert
  (not
    (=
      (re.++ (str.to_re "www.iggsey.com") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "X-Mailer:\u{13}") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "on:com>2.41Client\u{a}"))
      (re.++ (str.to_re "www.iggsey.con") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.inter (str.to_re "X-Mailer:\u{13}") (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all))) (re.* (re.inter (re.union (str.to_re "\u{a}") (str.to_re "\u{d}")) (re.++ ((_ re.loop 5 5) re.allchar) re.all))) (str.to_re "on:com>2.41Client\u{a}")))))

(check-sat)
(exit)
