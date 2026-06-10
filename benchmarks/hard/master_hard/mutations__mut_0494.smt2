;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance13736.smt2
;; Mutations:  literal_char_dec, range_expand_hi, intersect_max_len_10
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
;; R2: mutated (literal_char_dec, range_expand_hi, intersect_max_len_10)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "[Static") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "www.iggsey.comUser-Agent:X-Mailer:\u{13}Computer\u{a}")) (re.comp (re.++ (re.inter (str.to_re "[Static") ((_ re.loop 0 10) re.allchar)) (re.+ (re.union (re.range "0" ":") (re.range "A" "Z") (re.range "a" "z") (str.to_re "^"))) (str.to_re "www.iggsey.comUser-Agent:X-Mailer:\u{13}Computer\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "[Static") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re "www.iggsey.comUser-Agent:X-Mailer:\u{13}Computer\u{a}"))) (re.++ (re.inter (str.to_re "[Static") ((_ re.loop 0 10) re.allchar)) (re.+ (re.union (re.range "0" ":") (re.range "A" "Z") (re.range "a" "z") (str.to_re "^"))) (str.to_re "www.iggsey.comUser-Agent:X-Mailer:\u{13}Computer\u{a}"))))))

(check-sat)
(exit)
