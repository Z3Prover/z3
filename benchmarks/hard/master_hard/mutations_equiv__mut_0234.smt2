;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance06705.smt2
;; Mutations:  literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_inc)
(assert
  (not
    (=
      (re.++ ((_ re.loop 1 5) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9") (str.to_re "!") (str.to_re "@") (str.to_re "#") (str.to_re "$") (str.to_re "%") (str.to_re "^") (str.to_re "&") (str.to_re "*") (str.to_re "(") (re.range ")" "_") (str.to_re "=") (str.to_re "+") (str.to_re ";") (str.to_re ":") (str.to_re "'") (str.to_re "\u{22}") (str.to_re "|") (str.to_re "~") (str.to_re "`") (str.to_re "<") (str.to_re ">") (str.to_re "?") (str.to_re "/") (str.to_re "{") (str.to_re "}"))) (str.to_re "\u{a}"))
      (re.++ ((_ re.loop 1 5) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9") (str.to_re "!") (str.to_re "@") (str.to_re "#") (str.to_re "$") (str.to_re "%") (str.to_re "^") (str.to_re "&") (str.to_re "*") (str.to_re ")") (re.range ")" "_") (str.to_re "=") (str.to_re "+") (str.to_re ";") (str.to_re ":") (str.to_re "'") (str.to_re "\u{22}") (str.to_re "|") (str.to_re "~") (str.to_re "`") (str.to_re "<") (str.to_re ">") (str.to_re "?") (str.to_re "/") (str.to_re "{") (str.to_re "}"))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
