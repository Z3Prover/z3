;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance04693.smt2
;; Mutations:  range_shrink_hi, union_to_inter, star_to_plus
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
;; R2: mutated (range_shrink_hi, union_to_inter, star_to_plus)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "Port.") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "007") (re.+ (re.range "0" "9")) (str.to_re "Logsdl.web-nexus.net\u{a}")) (re.comp (re.++ (str.to_re "Port.") (re.+ (re.inter(str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "007") (re.+ (re.range "0" "8")) (str.to_re "Logsdl.web-nexus.net\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "Port.") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "007") (re.+ (re.range "0" "9")) (str.to_re "Logsdl.web-nexus.net\u{a}"))) (re.++ (str.to_re "Port.") (re.+ (re.inter(str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "007") (re.+ (re.range "0" "8")) (str.to_re "Logsdl.web-nexus.net\u{a}"))))))

(check-sat)
(exit)
