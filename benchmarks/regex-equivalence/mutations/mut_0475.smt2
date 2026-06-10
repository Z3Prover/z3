;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance05935.smt2
;; Mutations:  intersect_max_len_10, literal_char_inc, opt_to_required
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
;; R2: mutated (intersect_max_len_10, literal_char_inc, opt_to_required)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "<") (re.* (re.comp (str.to_re ">"))) (re.opt (str.to_re "\u{a}")) (re.* re.allchar) (str.to_re "=") (re.opt (re.union (str.to_re "\u{22}") (str.to_re "'"))) (re.opt (re.union (str.to_re "\u{22}") (str.to_re "'"))) (re.* re.allchar) (re.opt (str.to_re "\u{a}")) (re.* (re.comp (str.to_re "<"))) (str.to_re ">\u{a}") (re.* re.allchar) (str.to_re ".jpg")) (re.comp (re.++ (str.to_re "<") (re.* (re.comp (str.to_re ">"))) str.to_re "\u{a}") (re.* re.allchar) (str.to_re "=") (re.opt (re.union (str.to_re "\u{22}") (str.to_re "("))) (re.opt (re.union (str.to_re "\u{22}") (str.to_re "'"))) (re.* re.allchar) (re.inter (re.opt (str.to_re "\u{a}")) ((_ re.loop 0 10) re.allchar)) (re.* (re.comp (str.to_re "<"))) (str.to_re ">\u{a}") (re.* re.allchar) (str.to_re ".jpg")))) (re.inter (re.comp (re.++ (str.to_re "<") (re.* (re.comp (str.to_re ">"))) (re.opt (str.to_re "\u{a}")) (re.* re.allchar) (str.to_re "=") (re.opt (re.union (str.to_re "\u{22}") (str.to_re "'"))) (re.opt (re.union (str.to_re "\u{22}") (str.to_re "'"))) (re.* re.allchar) (re.opt (str.to_re "\u{a}")) (re.* (re.comp (str.to_re "<"))) (str.to_re ">\u{a}") (re.* re.allchar) (str.to_re ".jpg"))) (re.++ (str.to_re "<") (re.* (re.comp (str.to_re ">"))) str.to_re "\u{a}") (re.* re.allchar) (str.to_re "=") (re.opt (re.union (str.to_re "\u{22}") (str.to_re "("))) (re.opt (re.union (str.to_re "\u{22}") (str.to_re "'"))) (re.* re.allchar) (re.inter (re.opt (str.to_re "\u{a}")) ((_ re.loop 0 10) re.allchar)) (re.* (re.comp (str.to_re "<"))) (str.to_re ">\u{a}") (re.* re.allchar) (str.to_re ".jpg"))))))

(check-sat)
(exit)
