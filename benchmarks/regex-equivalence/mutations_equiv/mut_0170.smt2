;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance08578.smt2
;; Mutations:  range_expand_hi, intersect_ascii_printable_only
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_expand_hi, intersect_ascii_printable_only)
(assert
  (not
    (=
      (re.++ (str.to_re "User-Agent:") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "Owner:") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "Wordixqshv/qzccsServer\u{0}MyBYReferer:www.ccnnlc.com\u{13}\u{4}\u{0}\u{a}"))
      (re.++ (str.to_re "User-Agent:") (re.+ (re.inter (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_")) (re.* (re.range " " "~")))) (str.to_re "Owner:") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "{") (str.to_re "_"))) (str.to_re "Wordixqshv/qzccsServer\u{0}MyBYReferer:www.ccnnlc.com\u{13}\u{4}\u{0}\u{a}")))))

(check-sat)
(exit)
