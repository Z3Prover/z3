;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance09249.smt2
;; Mutations:  intersect_no_dot_dot, intersect_no_slash_slash, literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_dot_dot, intersect_no_slash_slash, literal_char_inc)
(assert
  (not
    (=
      (re.++ (str.to_re "Contact") (re.+ (re.range "0" "9")) (str.to_re "Host:") (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (str.to_re "User-Agent:Host:MailHost:MSNLOGOVN\u{a}"))
      (re.++ (str.to_re "Contacu") (re.inter (re.+ (re.range "0" "9")) (re.comp (re.++ re.all (str.to_re "//") re.all))) (str.to_re "Host:") (re.inter (re.* (re.union (str.to_re "\u{a}") (str.to_re "\u{d}"))) (re.comp (re.++ re.all (str.to_re "..") re.all))) (str.to_re "User-Agent:Host:MailHost:MSNLOGOVN\u{a}")))))

(check-sat)
(exit)
