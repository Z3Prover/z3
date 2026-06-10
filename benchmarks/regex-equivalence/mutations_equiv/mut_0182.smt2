;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11383.smt2
;; Mutations:  intersect_no_alnum3
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_alnum3)
(assert
  (not
    (=
      (re.++ (str.to_re "Toolbar") (re.+ (re.range "0" "9")) (str.to_re "ServerLiteToolbardailywww.cameup.com\u{13}\u{a}"))
      (re.++ (str.to_re "Toolbar") (re.inter (re.+ (re.range "0" "9")) (re.comp (re.++ re.all ((_ re.loop 3 3) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) re.all))) (str.to_re "ServerLiteToolbardailywww.cameup.com\u{13}\u{a}")))))

(check-sat)
(exit)
