;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance09005.smt2
;; Mutations:  literal_char_dec, literal_char_dec
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
;; R2: mutated (literal_char_dec, literal_char_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "IP") (re.* re.allchar) (str.to_re "encoder") (re.+ (re.range "0" "9")) (str.to_re "SAHPORT-User-Agent:\u{a}")) (re.comp (re.++ (str.to_re "IO") (re.* re.allchar) (str.to_re "encodeq") (re.+ (re.range "0" "9")) (str.to_re "SAHPORT-User-Agent:\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "IP") (re.* re.allchar) (str.to_re "encoder") (re.+ (re.range "0" "9")) (str.to_re "SAHPORT-User-Agent:\u{a}"))) (re.++ (str.to_re "IO") (re.* re.allchar) (str.to_re "encodeq") (re.+ (re.range "0" "9")) (str.to_re "SAHPORT-User-Agent:\u{a}"))))))

(check-sat)
(exit)
