;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance08178.smt2
;; Mutations:  intersect_no_digits4, literal_char_dec, literal_char_inc
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
;; R2: mutated (intersect_no_digits4, literal_char_dec, literal_char_inc)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "Toolbar") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "url=") (re.+ (re.range "0" "9")) (str.to_re "Host:Welcome/communicatortbGateCrasher\u{a}")) (re.comp (re.++ (str.to_re "Toolbas") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "url<") (re.+ (re.range "0" "9")) (re.inter (str.to_re "Host:Welcome/communicatortbGateCrasher\u{a}") (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all)))))) (re.inter (re.comp (re.++ (str.to_re "Toolbar") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "url=") (re.+ (re.range "0" "9")) (str.to_re "Host:Welcome/communicatortbGateCrasher\u{a}"))) (re.++ (str.to_re "Toolbas") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "url<") (re.+ (re.range "0" "9")) (re.inter (str.to_re "Host:Welcome/communicatortbGateCrasher\u{a}") (re.comp (re.++ re.all ((_ re.loop 4 4) (re.range "0" "9")) re.all))))))))

(check-sat)
(exit)
