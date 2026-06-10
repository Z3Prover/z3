;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance14080.smt2
;; Mutations:  literal_char_inc, union_to_inter
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_inc, union_to_inter)
(assert
  (not
    (=
      (re.union (re.++ (re.union (re.++ (re.* (str.to_re "s")) (str.to_re "ftp") (re.* (str.to_re "s"))) (re.++ (str.to_re "http") (re.* (str.to_re "s"))) (str.to_re "mailto") (str.to_re "news") (str.to_re "file") (str.to_re "webcal")) (str.to_re ":") (re.* (re.comp (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))) (re.++ (str.to_re "\u{a}") (re.* (re.comp (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")))) (str.to_re "www") re.allchar))
      (re.union (re.++ (re.inter (re.++ (re.* (str.to_re "s")) (str.to_re "ftp") (re.* (str.to_re "s"))) (re.++ (str.to_re "http") (re.* (str.to_re "s"))) (str.to_re "mailto") (str.to_re "newt") (str.to_re "file") (str.to_re "webcal")) (str.to_re ":") (re.* (re.comp (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))) (re.++ (str.to_re "\u{a}") (re.* (re.comp (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")))) (str.to_re "www") re.allchar)))))

(check-sat)
(exit)
