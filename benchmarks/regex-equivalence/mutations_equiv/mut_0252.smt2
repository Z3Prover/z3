;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance13917.smt2
;; Mutations:  literal_char_inc, union_to_inter, literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_inc, union_to_inter, literal_char_dec)
(assert
  (not
    (=
      (re.++ (str.to_re "/&") (re.union (re.++ (str.to_re "db") (re.union (str.to_re "username") (str.to_re "password"))) (re.++ (str.to_re "cp") (re.union (str.to_re "username") (str.to_re "password") (str.to_re "domain")))) (str.to_re "=") (re.* (re.comp (str.to_re "&"))) (re.union (str.to_re "'") (str.to_re "%27")) (re.* (re.comp (str.to_re "&"))) (re.union (str.to_re "$(") (str.to_re "%3b") (str.to_re "%60") (str.to_re "%24%28") (str.to_re ";") (str.to_re "`")) (str.to_re "/Pmi\u{a}"))
      (re.++ (str.to_re "/&") (re.union (re.++ (str.to_re "db") (re.union (str.to_re "username") (str.to_re "passworc"))) (re.++ (str.to_re "cp") (re.inter (str.to_re "username") (str.to_re "password") (str.to_re "domain")))) (str.to_re "=") (re.* (re.comp (str.to_re "&"))) (re.union (str.to_re "'") (str.to_re "%28")) (re.* (re.comp (str.to_re "&"))) (re.union (str.to_re "$(") (str.to_re "%3b") (str.to_re "%60") (str.to_re "%24%28") (str.to_re ";") (str.to_re "`")) (str.to_re "/Pmi\u{a}")))))

(check-sat)
(exit)
