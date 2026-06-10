;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00618.smt2
;; Mutations:  literal_char_inc, literal_char_inc
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
;; R2: mutated (literal_char_inc, literal_char_inc)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "\u{a}") ((_ re.loop 1 1) (re.union (str.to_re "mailto:") (re.++ (re.union (str.to_re "news") (re.++ (re.union (str.to_re "ht") (str.to_re "f")) (str.to_re "tp") (re.opt (str.to_re "s")))) (str.to_re "://")))) (re.+ (re.comp (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))) (re.comp (re.++ (str.to_re "\u{a}") ((_ re.loop 1 1) (re.union (str.to_re "mailto;") (re.++ (re.union (str.to_re "news") (re.++ (re.union (str.to_re "ht") (str.to_re "g")) (str.to_re "tp") (re.opt (str.to_re "s")))) (str.to_re "://")))) (re.+ (re.comp (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))))) (re.inter (re.comp (re.++ (str.to_re "\u{a}") ((_ re.loop 1 1) (re.union (str.to_re "mailto:") (re.++ (re.union (str.to_re "news") (re.++ (re.union (str.to_re "ht") (str.to_re "f")) (str.to_re "tp") (re.opt (str.to_re "s")))) (str.to_re "://")))) (re.+ (re.comp (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")))))) (re.++ (str.to_re "\u{a}") ((_ re.loop 1 1) (re.union (str.to_re "mailto;") (re.++ (re.union (str.to_re "news") (re.++ (re.union (str.to_re "ht") (str.to_re "g")) (str.to_re "tp") (re.opt (str.to_re "s")))) (str.to_re "://")))) (re.+ (re.comp (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")))))))))

(check-sat)
(exit)
