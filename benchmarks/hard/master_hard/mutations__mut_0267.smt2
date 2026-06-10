;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance03824.smt2
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
    (re.union (re.inter (re.++ (str.to_re "GmbH") (re.+ (re.range "0" "9")) (str.to_re "Host:") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "adblock.linkz.comUser-Agent:email\u{a}")) (re.comp (re.++ (str.to_re "GmbH") (re.+ (re.range "0" "9")) (str.to_re "Host9") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "^"))) (str.to_re "adblock.linkz.comUser-Agent:email\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "GmbH") (re.+ (re.range "0" "9")) (str.to_re "Host:") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "adblock.linkz.comUser-Agent:email\u{a}"))) (re.++ (str.to_re "GmbH") (re.+ (re.range "0" "9")) (str.to_re "Host9") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "^"))) (str.to_re "adblock.linkz.comUser-Agent:email\u{a}"))))))

(check-sat)
(exit)
