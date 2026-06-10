;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance04831.smt2
;; Mutations:  range_shrink_lo, literal_char_dec, star_to_plus
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo, literal_char_dec, star_to_plus)
(assert
  (not
    (=
      (re.++ (str.to_re "/Referer: ") (re.* (re.range " " "~")) (str.to_re "/wp-admin/") (re.+ (re.union (re.range "a" "z") (re.range "0" "9") (str.to_re "-"))) (str.to_re ".php\u{d}\u{a}/Hi\u{a}"))
      (re.++ (str.to_re "/Referer: ") (re.+ (re.range " " "~")) (str.to_re "/wp-admin.") (re.+ (re.union (re.range "a" "z") (re.range "1" "9") (str.to_re "-"))) (str.to_re ".php\u{d}\u{a}/Hi\u{a}")))))

(check-sat)
(exit)
