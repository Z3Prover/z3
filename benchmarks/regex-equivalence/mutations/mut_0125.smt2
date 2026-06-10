;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance08677.smt2
;; Mutations:  intersect_ascii_printable_only
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
;; R2: mutated (intersect_ascii_printable_only)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "/GET /plus.asp?") (re.* (re.union (str.to_re "\u{d}") (str.to_re "\u{a}"))) (str.to_re "query=") ((_ re.loop 2 40) (re.union (re.range "a" "z") (re.range "0" "9") (str.to_re "+") (str.to_re "/"))) ((_ re.loop 0 2) (str.to_re "@")) (str.to_re "/i\u{a}")) (re.comp (re.++ (str.to_re "/GET /plus.asp?") (re.* (re.union (str.to_re "\u{d}") (str.to_re "\u{a}"))) (re.inter (str.to_re "query=") (re.* (re.range " " "~"))) ((_ re.loop 2 40) (re.union (re.range "a" "z") (re.range "0" "9") (str.to_re "+") (str.to_re "/"))) ((_ re.loop 0 2) (str.to_re "@")) (str.to_re "/i\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "/GET /plus.asp?") (re.* (re.union (str.to_re "\u{d}") (str.to_re "\u{a}"))) (str.to_re "query=") ((_ re.loop 2 40) (re.union (re.range "a" "z") (re.range "0" "9") (str.to_re "+") (str.to_re "/"))) ((_ re.loop 0 2) (str.to_re "@")) (str.to_re "/i\u{a}"))) (re.++ (str.to_re "/GET /plus.asp?") (re.* (re.union (str.to_re "\u{d}") (str.to_re "\u{a}"))) (re.inter (str.to_re "query=") (re.* (re.range " " "~"))) ((_ re.loop 2 40) (re.union (re.range "a" "z") (re.range "0" "9") (str.to_re "+") (str.to_re "/"))) ((_ re.loop 0 2) (str.to_re "@")) (str.to_re "/i\u{a}"))))))

(check-sat)
(exit)
