;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance05735.smt2
;; Mutations:  range_expand_hi
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_expand_hi)
(assert
  (not
    (=
      (re.++ (str.to_re "Report") (re.range "0" "9") (str.to_re "DmInf^infoSimpsonUser-Agent:Clientwww.internet-optimizer.com\u{a}"))
      (re.++ (str.to_re "Report") (re.range "0" ":") (str.to_re "DmInf^infoSimpsonUser-Agent:Clientwww.internet-optimizer.com\u{a}")))))

(check-sat)
(exit)
