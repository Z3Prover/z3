;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance14867.smt2
;; Mutations:  intersect_max_len_20
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
;; R2: mutated (intersect_max_len_20)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "/\u{d}\u{a}Host: ") (re.+ (re.union (str.to_re "\u{d}") (str.to_re "\u{a}") (str.to_re "."))) (str.to_re ".") (re.+ (re.union (str.to_re "\u{d}") (str.to_re "\u{a}") (str.to_re "."))) (re.opt (re.++ (str.to_re ":") ((_ re.loop 1 5) (re.range "0" "9")))) (str.to_re "\u{d}\u{a}\u{d}\u{a}/H\u{a}")) (re.comp (re.++ (re.inter (str.to_re "/\u{d}\u{a}Host: ") ((_ re.loop 0 20) re.allchar)) (re.+ (re.union (str.to_re "\u{d}") (str.to_re "\u{a}") (str.to_re "."))) (str.to_re ".") (re.+ (re.union (str.to_re "\u{d}") (str.to_re "\u{a}") (str.to_re "."))) (re.opt (re.++ (str.to_re ":") ((_ re.loop 1 5) (re.range "0" "9")))) (str.to_re "\u{d}\u{a}\u{d}\u{a}/H\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "/\u{d}\u{a}Host: ") (re.+ (re.union (str.to_re "\u{d}") (str.to_re "\u{a}") (str.to_re "."))) (str.to_re ".") (re.+ (re.union (str.to_re "\u{d}") (str.to_re "\u{a}") (str.to_re "."))) (re.opt (re.++ (str.to_re ":") ((_ re.loop 1 5) (re.range "0" "9")))) (str.to_re "\u{d}\u{a}\u{d}\u{a}/H\u{a}"))) (re.++ (re.inter (str.to_re "/\u{d}\u{a}Host: ") ((_ re.loop 0 20) re.allchar)) (re.+ (re.union (str.to_re "\u{d}") (str.to_re "\u{a}") (str.to_re "."))) (str.to_re ".") (re.+ (re.union (str.to_re "\u{d}") (str.to_re "\u{a}") (str.to_re "."))) (re.opt (re.++ (str.to_re ":") ((_ re.loop 1 5) (re.range "0" "9")))) (str.to_re "\u{d}\u{a}\u{d}\u{a}/H\u{a}"))))))

(check-sat)
(exit)
