;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance04586.smt2
;; Mutations:  intersect_no_upper2
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
;; R2: mutated (intersect_no_upper2)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "/PRIVMSG #new :\u{2}[") (re.union (str.to_re "GOOGLE") (str.to_re "SCAN")) (str.to_re "]\u{2} Scanning/\u{a}")) (re.comp (re.++ (str.to_re "/PRIVMSG #new :\u{2}[") (re.inter (re.union (str.to_re "GOOGLE") (str.to_re "SCAN")) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) (str.to_re "]\u{2} Scanning/\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "/PRIVMSG #new :\u{2}[") (re.union (str.to_re "GOOGLE") (str.to_re "SCAN")) (str.to_re "]\u{2} Scanning/\u{a}"))) (re.++ (str.to_re "/PRIVMSG #new :\u{2}[") (re.inter (re.union (str.to_re "GOOGLE") (str.to_re "SCAN")) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) (str.to_re "]\u{2} Scanning/\u{a}"))))))

(check-sat)
(exit)
