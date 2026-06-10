;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance15361.smt2
;; Mutations:  intersect_no_slash_slash
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_slash_slash)
(assert
  (not
    (=
      (re.++ (re.union (re.++ (re.+ (re.union (str.to_re "V") (str.to_re "v"))) (re.opt (re.++ (str.to_re "erdade") (re.opt (str.to_re "iro"))))) (re.++ (re.+ (re.union (str.to_re "F") (str.to_re "f"))) (re.opt (re.++ (str.to_re "als") (re.union (str.to_re "e") (str.to_re "o"))))) (re.++ (re.+ (re.union (str.to_re "T") (str.to_re "t"))) (re.opt (str.to_re "rue"))) (str.to_re "0") (re.++ (re.opt (re.union (str.to_re "+") (str.to_re "-"))) (str.to_re "1"))) (str.to_re "\u{a}"))
      (re.++ (re.union (re.++ (re.+ (re.union (str.to_re "V") (str.to_re "v"))) (re.opt (re.++ (str.to_re "erdade") (re.opt (str.to_re "iro"))))) (re.++ (re.+ (re.inter (re.union (str.to_re "F") (str.to_re "f")) (re.comp (re.++ re.all (str.to_re "//") re.all)))) (re.opt (re.++ (str.to_re "als") (re.union (str.to_re "e") (str.to_re "o"))))) (re.++ (re.+ (re.union (str.to_re "T") (str.to_re "t"))) (re.opt (str.to_re "rue"))) (str.to_re "0") (re.++ (re.opt (re.union (str.to_re "+") (str.to_re "-"))) (str.to_re "1"))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
