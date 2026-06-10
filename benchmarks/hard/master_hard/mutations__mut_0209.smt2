;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance03275.smt2
;; Mutations:  intersect_no_digits4, literal_char_dec, range_expand_hi
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
;; R2: mutated (intersect_no_digits4, literal_char_dec, range_expand_hi)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "Host:") (re.+ (re.range "0" "9")) (str.to_re "rprpgbnrppb/ci") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "RXFilteredDmInf^\u{a}")) (re.comp (re.++ (str.to_re "Host:") (re.+ (re.range "0" ":")) (str.to_re "rprpgbnrppb/ch") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (re.inter (str.to_re "RXFilteredDmInf^\u{a}") (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all)))))) (re.inter (re.comp (re.++ (str.to_re "Host:") (re.+ (re.range "0" "9")) (str.to_re "rprpgbnrppb/ci") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "RXFilteredDmInf^\u{a}"))) (re.++ (str.to_re "Host:") (re.+ (re.range "0" ":")) (str.to_re "rprpgbnrppb/ch") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (re.inter (str.to_re "RXFilteredDmInf^\u{a}") (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all))))))))

(check-sat)
(exit)
