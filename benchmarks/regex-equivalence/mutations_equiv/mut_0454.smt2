;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance06182.smt2
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
      (re.++ (str.to_re "<img") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.* (re.++ (re.union (str.to_re "width") (str.to_re "height") (str.to_re "alt") (str.to_re "align") (str.to_re "style")) (str.to_re "=\u{22}") (re.* (re.comp (str.to_re "\u{22}"))) (str.to_re "\u{22}") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")))) (str.to_re "src=\u{22}") (re.+ (re.++ (re.opt (str.to_re "/")) (re.union (re.range "a" "z") (re.range "0" "9") (str.to_re "_") (str.to_re "-")) (re.opt (str.to_re "/")))) (str.to_re ".") (re.union (str.to_re "png") (str.to_re "jpg") (str.to_re "jpeg") (str.to_re "gif")) (str.to_re "\u{22}") (re.* (re.++ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.union (str.to_re "width") (str.to_re "height") (str.to_re "alt") (str.to_re "align") (str.to_re "style")) (str.to_re "=\u{22}") (re.* (re.comp (str.to_re "\u{22}"))) (str.to_re "\u{22}"))) (re.* (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "/>\u{a}"))
      (re.++ (str.to_re "<img") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.* (re.++ (re.union (str.to_re "width") (str.to_re "height") (str.to_re "alt") (str.to_re "align") (str.to_re "style")) (str.to_re "=\u{22}") (re.* (re.comp (str.to_re "\u{22}"))) (str.to_re "\u{22}") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")))) (str.to_re "src=\u{22}") (re.+ (re.++ (re.opt (str.to_re "/")) (re.union (re.range "a" "z") (re.range "0" "9") (str.to_re "_") (str.to_re "-")) (re.opt (str.to_re "/")))) (str.to_re ".") (re.union (str.to_re "pnh") (str.to_re "jpg") (str.to_re "jpeg") (str.to_re "gie")) (str.to_re "\u{22}") (re.* (re.++ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.union (str.to_re "width") (str.to_re "height") (str.to_re "alt") (str.to_re "align") (str.to_re "style")) (str.to_re "=\u{22}") (re.* (re.comp (str.to_re "\u{22}"))) (str.to_re "\u{22}"))) (re.* (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "/>\u{a}")))))

(check-sat)
(exit)
