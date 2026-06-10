;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance04716.smt2
;; Mutations:  intersect_no_at_sign, literal_char_inc
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
;; R2: mutated (intersect_no_at_sign, literal_char_inc)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "Subject:") (re.+ (re.range "0" "9")) (str.to_re "zmnjgmomgbdz/zzmw.gzt\u{a}")) (re.comp (re.++ (str.to_re "Subject;") (re.inter (re.+ (re.range "0" "9")) (re.comp (re.++ re.all (str.to_re "@") re.all))) (str.to_re "zmnjgmomgbdz/zzmw.gzt\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "Subject:") (re.+ (re.range "0" "9")) (str.to_re "zmnjgmomgbdz/zzmw.gzt\u{a}"))) (re.++ (str.to_re "Subject;") (re.inter (re.+ (re.range "0" "9")) (re.comp (re.++ re.all (str.to_re "@") re.all))) (str.to_re "zmnjgmomgbdz/zzmw.gzt\u{a}"))))))

(check-sat)
(exit)
