;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance13842.smt2
;; Mutations:  intersect_no_alnum5, literal_char_dec
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
;; R2: mutated (intersect_no_alnum5, literal_char_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "Anal") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "news") (re.* re.allchar) (str.to_re "User-Agent:\u{a}")) (re.comp (re.++ (str.to_re "Anal") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "newr") (re.* re.allchar) (re.inter (str.to_re "User-Agent:\u{a}") (re.comp (re.++ re.all ((_ re.loop 5 5) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) re.all)))))) (re.inter (re.comp (re.++ (str.to_re "Anal") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "news") (re.* re.allchar) (str.to_re "User-Agent:\u{a}"))) (re.++ (str.to_re "Anal") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "newr") (re.* re.allchar) (re.inter (str.to_re "User-Agent:\u{a}") (re.comp (re.++ re.all ((_ re.loop 5 5) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) re.all))))))))

(check-sat)
(exit)
