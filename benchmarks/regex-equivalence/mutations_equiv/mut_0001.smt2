;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance10432.smt2
;; Mutations:  bound_upper_dec, bound_upper_dec, intersect_max_len_10
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (bound_upper_dec, bound_upper_dec, intersect_max_len_10)
(assert
  (not
    (=
      (re.union (re.opt (re.++ (re.union (str.to_re "0") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re ".") ((_ re.loop 0 2) (re.range "0" "9")) ((_ re.loop 0 2) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))) (re.opt (re.++ (str.to_re ".") ((_ re.loop 0 2) (re.++ (re.range "0" "9") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")))))) (re.opt (re.++ ((_ re.loop 0 4) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.opt (str.to_re "1")) (str.to_re ".") ((_ re.loop 0 2) (str.to_re "0")) ((_ re.loop 0 4) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))) (re.opt (re.++ ((_ re.loop 0 4) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.opt (str.to_re "1")) ((_ re.loop 0 4) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))) (re.opt (re.++ ((_ re.loop 0 4) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) ((_ re.loop 0 4) (str.to_re "0")) (re.opt (str.to_re "1")) ((_ re.loop 0 4) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))) (re.opt (re.++ ((_ re.loop 0 4) (str.to_re "0")) ((_ re.loop 0 4) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))) (re.++ (re.opt (re.++ ((_ re.loop 0 3) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) ((_ re.loop 0 3) (str.to_re "0")) ((_ re.loop 1 1) (str.to_re ".")) ((_ re.loop 0 2) (re.range "0" "9")) ((_ re.loop 0 2) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))) (str.to_re "\u{a}")))
      (re.union (re.opt (re.++ (re.union (str.to_re "0") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re ".") ((_ re.loop 0 2) (re.range "0" "9")) ((_ re.loop 0 2) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))) (re.inter (re.opt (re.++ (str.to_re ".") ((_ re.loop 0 2) (re.++ (re.range "0" "9") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")))))) ((_ re.loop 0 10) re.allchar)) (re.opt (re.++ ((_ re.loop 0 4) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.opt (str.to_re "1")) (str.to_re ".") ((_ re.loop 0 2) (str.to_re "0")) ((_ re.loop 0 4) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))) (re.opt (re.++ ((_ re.loop 0 4) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.opt (str.to_re "1")) ((_ re.loop 0 3) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))) (re.opt (re.++ ((_ re.loop 0 3) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) ((_ re.loop 0 4) (str.to_re "0")) (re.opt (str.to_re "1")) ((_ re.loop 0 4) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))) (re.opt (re.++ ((_ re.loop 0 4) (str.to_re "0")) ((_ re.loop 0 4) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))) (re.++ (re.opt (re.++ ((_ re.loop 0 3) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) ((_ re.loop 0 3) (str.to_re "0")) ((_ re.loop 1 1) (str.to_re ".")) ((_ re.loop 0 2) (re.range "0" "9")) ((_ re.loop 0 2) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
