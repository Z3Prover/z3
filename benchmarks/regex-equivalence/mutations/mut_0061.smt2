;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance05015.smt2
;; Mutations:  bound_upper_dec
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
;; R2: mutated (bound_upper_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.comp (str.to_re "_")) (re.+ (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9") (str.to_re "_"))) (re.comp (str.to_re "_")) ((_ re.loop 1 1) (str.to_re "@")) (re.+ (re.range "a" "z")) ((_ re.loop 1 1) (str.to_re ".")) (re.union ((_ re.loop 2 3) (re.range "a" "z")) (re.++ ((_ re.loop 2 3) (re.range "a" "z")) ((_ re.loop 1 1) (str.to_re ".")) ((_ re.loop 2 3) (re.range "a" "z")))) (str.to_re "\u{a}")) (re.comp (re.++ (re.comp (str.to_re "_")) (re.+ (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9") (str.to_re "_"))) (re.comp (str.to_re "_")) ((_ re.loop 1 1) (str.to_re "@")) (re.+ (re.range "a" "z")) ((_ re.loop 1 1) (str.to_re ".")) (re.union ((_ re.loop 2 3) (re.range "a" "z")) (re.++ ((_ re.loop 2 3) (re.range "a" "z")) ((_ re.loop 1 1) (str.to_re ".")) ((_ re.loop 2 2) (re.range "a" "z")))) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.comp (str.to_re "_")) (re.+ (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9") (str.to_re "_"))) (re.comp (str.to_re "_")) ((_ re.loop 1 1) (str.to_re "@")) (re.+ (re.range "a" "z")) ((_ re.loop 1 1) (str.to_re ".")) (re.union ((_ re.loop 2 3) (re.range "a" "z")) (re.++ ((_ re.loop 2 3) (re.range "a" "z")) ((_ re.loop 1 1) (str.to_re ".")) ((_ re.loop 2 3) (re.range "a" "z")))) (str.to_re "\u{a}"))) (re.++ (re.comp (str.to_re "_")) (re.+ (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9") (str.to_re "_"))) (re.comp (str.to_re "_")) ((_ re.loop 1 1) (str.to_re "@")) (re.+ (re.range "a" "z")) ((_ re.loop 1 1) (str.to_re ".")) (re.union ((_ re.loop 2 3) (re.range "a" "z")) (re.++ ((_ re.loop 2 3) (re.range "a" "z")) ((_ re.loop 1 1) (str.to_re ".")) ((_ re.loop 2 2) (re.range "a" "z")))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
