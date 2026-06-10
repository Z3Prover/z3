;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance09028.smt2
;; Mutations:  range_shrink_lo, literal_char_dec, literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo, literal_char_dec, literal_char_dec)
(assert
  (not
    (=
      (re.++ (str.to_re "/Referer:") (re.+ (re.union (str.to_re "\u{d}") (str.to_re "\u{a}"))) (str.to_re "/.html\u{d}/Hsm\u{a}") ((_ re.loop 32 32) (re.union (str.to_re "_") (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (re.* (re.union (str.to_re "_") (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))))
      (re.++ (str.to_re "/Referer9") (re.+ (re.union (str.to_re "\u{d}") (str.to_re "\u{a}"))) (str.to_re "/.html\u{d}/Hsm\u{a}") ((_ re.loop 32 32) (re.union (str.to_re "_") (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (re.* (re.union (str.to_re "^") (re.range "0" "9") (re.range "B" "Z") (re.range "a" "z") (str.to_re "_")))))))

(check-sat)
(exit)
