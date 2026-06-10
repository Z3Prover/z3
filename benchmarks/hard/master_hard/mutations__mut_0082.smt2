;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00570.smt2
;; Mutations:  intersect_no_at_sign, union_to_inter, literal_char_dec
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
;; R2: mutated (intersect_no_at_sign, union_to_inter, literal_char_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "ConnectionUser-Agent:") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "www.fast-finder.com\u{a}")) (re.comp (re.++ (str.to_re "ConnectionUser-Agent9") (re.inter(str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.inter (str.to_re "www.fast-finder.com\u{a}") (re.comp (re.++ re.all (str.to_re "@") re.all)))))) (re.inter (re.comp (re.++ (str.to_re "ConnectionUser-Agent:") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "www.fast-finder.com\u{a}"))) (re.++ (str.to_re "ConnectionUser-Agent9") (re.inter(str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.inter (str.to_re "www.fast-finder.com\u{a}") (re.comp (re.++ re.all (str.to_re "@") re.all))))))))

(check-sat)
(exit)
