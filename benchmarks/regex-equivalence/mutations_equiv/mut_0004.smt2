;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance14824.smt2
;; Mutations:  plus_to_star, range_shrink_lo, literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (plus_to_star, range_shrink_lo, literal_char_inc)
(assert
  (not
    (=
      (re.++ (str.to_re "X-OSSproxy:") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "+Version+") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "fast-look.comwww.maxifiles.com\u{a}"))
      (re.++ (str.to_re "X-OSSproxy;") (re.+ (re.union (re.range "1" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "+Version+") (re.* (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "fast-look.comwww.maxifiles.com\u{a}")))))

(check-sat)
(exit)
