;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance05358.smt2
;; Mutations:  literal_char_inc
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
;; R2: mutated (literal_char_inc)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "http://www") re.allchar (str.to_re "mail-password-recovery") re.allchar (str.to_re "com/\u{a}")) (re.comp (re.++ (str.to_re "http://www") re.allchar (str.to_re "mail-password-recoverz") re.allchar (str.to_re "com/\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "http://www") re.allchar (str.to_re "mail-password-recovery") re.allchar (str.to_re "com/\u{a}"))) (re.++ (str.to_re "http://www") re.allchar (str.to_re "mail-password-recoverz") re.allchar (str.to_re "com/\u{a}"))))))

(check-sat)
(exit)
