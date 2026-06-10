;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance04748.smt2
;; Mutations:  intersect_ascii_printable_only, intersect_max_len_10, intersect_no_upper2
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
;; R2: mutated (intersect_ascii_printable_only, intersect_max_len_10, intersect_no_upper2)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "User-Agent:") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "offers.bullseye-network.com") (re.+ (re.range "0" "9")) (str.to_re "FTPsearch.dropspam.com\u{a}")) (re.comp (re.++ (str.to_re "User-Agent:") (re.inter (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) (re.inter (str.to_re "offers.bullseye-network.com") ((_ re.loop 0 10) re.allchar)) (re.inter (re.+ (re.range "0" "9")) (re.* (re.range " " "~"))) (str.to_re "FTPsearch.dropspam.com\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "User-Agent:") (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "offers.bullseye-network.com") (re.+ (re.range "0" "9")) (str.to_re "FTPsearch.dropspam.com\u{a}"))) (re.++ (str.to_re "User-Agent:") (re.inter (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) (re.inter (str.to_re "offers.bullseye-network.com") ((_ re.loop 0 10) re.allchar)) (re.inter (re.+ (re.range "0" "9")) (re.* (re.range " " "~"))) (str.to_re "FTPsearch.dropspam.com\u{a}"))))))

(check-sat)
(exit)
