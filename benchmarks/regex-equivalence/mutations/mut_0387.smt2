;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance01539.smt2
;; Mutations:  plus_to_star
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
;; R2: mutated (plus_to_star)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "SbAts") (re.+ (re.range "0" "9")) (str.to_re "dcww.dmcast.comdistID=\u{a}")) (re.comp (re.++ (str.to_re "SbAts") (re.* (re.range "0" "9")) (str.to_re "dcww.dmcast.comdistID=\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "SbAts") (re.+ (re.range "0" "9")) (str.to_re "dcww.dmcast.comdistID=\u{a}"))) (re.++ (str.to_re "SbAts") (re.* (re.range "0" "9")) (str.to_re "dcww.dmcast.comdistID=\u{a}"))))))

(check-sat)
(exit)
