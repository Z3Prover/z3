;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance10441.smt2
;; Mutations:  intersect_no_upper2, literal_char_inc, intersect_no_digits4
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)

(declare-const x String)

;; R1: original
;; R2: mutated (intersect_no_upper2, literal_char_inc, intersect_no_digits4)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "tv.180solutions.com") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "have") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "Dayspassword;0;Incorrect\u{a}")) (re.comp (re.++ (re.inter (str.to_re "tv.180solutions.com") (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all))) (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "havf") (re.+ (re.inter (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all)))) (str.to_re "Dayspassword;0;Incorrect\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "tv.180solutions.com") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "have") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "Dayspassword;0;Incorrect\u{a}"))) (re.++ (re.inter (str.to_re "tv.180solutions.com") (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all))) (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "havf") (re.+ (re.inter (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all)))) (str.to_re "Dayspassword;0;Incorrect\u{a}"))))))

(check-sat)
(exit)
