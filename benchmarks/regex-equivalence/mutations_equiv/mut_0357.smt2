;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00020.smt2
;; Mutations:  literal_char_dec, literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_dec, literal_char_dec)
(assert
  (not
    (=
      (re.++ (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c")) re.allchar (re.* (re.++ (str.to_re "a") re.allchar (str.to_re "b"))) re.allchar (re.+ (str.to_re "b")) re.allchar (str.to_re "c\u{a}"))
      (re.++ (re.union (str.to_re "a") (str.to_re "b") (str.to_re "b")) re.allchar (re.* (re.++ (str.to_re "a") re.allchar (str.to_re "b"))) re.allchar (re.+ (str.to_re "a")) re.allchar (str.to_re "c\u{a}")))))

(check-sat)
(exit)
