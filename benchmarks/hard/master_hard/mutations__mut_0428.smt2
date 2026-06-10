;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance09446.smt2
;; Mutations:  intersect_max_len_10, intersect_no_at_sign, literal_char_inc
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
;; R2: mutated (intersect_max_len_10, intersect_no_at_sign, literal_char_inc)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "Google") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "-~-GREATHost:FILESIZE>\u{13}\u{a}")) (re.comp (re.++ (str.to_re "Googlf") (re.inter (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.comp (re.++ re.all (str.to_re "@") re.all))) (re.inter (str.to_re "-~-GREATHost:FILESIZE>\u{13}\u{a}") ((_ re.loop 0 10) re.allchar))))) (re.inter (re.comp (re.++ (str.to_re "Google") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "-~-GREATHost:FILESIZE>\u{13}\u{a}"))) (re.++ (str.to_re "Googlf") (re.inter (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.comp (re.++ re.all (str.to_re "@") re.all))) (re.inter (str.to_re "-~-GREATHost:FILESIZE>\u{13}\u{a}") ((_ re.loop 0 10) re.allchar)))))))

(check-sat)
(exit)
