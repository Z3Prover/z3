;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance05997.smt2
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
    (re.union (re.inter (re.union (re.++ (re.union (str.to_re "Sun") (str.to_re "Mon") (re.++ (str.to_re "T") (re.union (str.to_re "ues") (str.to_re "hurs"))) (str.to_re "Fri")) (re.opt (re.union (str.to_re "day") (str.to_re ".")))) (re.++ (str.to_re "Wed") (re.opt (re.union (str.to_re ".") (str.to_re "nesday")))) (re.++ (str.to_re "Sat") (re.opt (re.union (str.to_re ".") (str.to_re "urday")))) (re.++ (str.to_re "T") (re.union (re.++ (str.to_re "u") (re.opt (str.to_re "e"))) (re.++ (str.to_re "h") (re.opt (str.to_re "u")) (re.opt (str.to_re "r")))) (re.opt (str.to_re ".")) (str.to_re "\u{a}"))) (re.comp (re.union (re.++ (re.union (str.to_re "Sun") (str.to_re "Mom") (re.++ (str.to_re "S") (re.union (str.to_re "ues") (str.to_re "hurs"))) (str.to_re "Fri")) (re.opt (re.union (str.to_re "day") (str.to_re ".")))) (re.++ (str.to_re "Wed") (re.opt (re.union (str.to_re ".") (str.to_re "nesday")))) (re.++ (str.to_re "Sat") (re.opt (re.union (str.to_re ".") (str.to_re "urday")))) (re.++ (str.to_re "T") (re.union (re.++ (str.to_re "u") (re.opt (str.to_re "e"))) (re.++ (str.to_re "h") (re.opt (str.to_re "u")) (re.opt (str.to_re "r")))) (re.opt (str.to_re ".")) (str.to_re "\u{a}"))))) (re.inter (re.comp (re.union (re.++ (re.union (str.to_re "Sun") (str.to_re "Mon") (re.++ (str.to_re "T") (re.union (str.to_re "ues") (str.to_re "hurs"))) (str.to_re "Fri")) (re.opt (re.union (str.to_re "day") (str.to_re ".")))) (re.++ (str.to_re "Wed") (re.opt (re.union (str.to_re ".") (str.to_re "nesday")))) (re.++ (str.to_re "Sat") (re.opt (re.union (str.to_re ".") (str.to_re "urday")))) (re.++ (str.to_re "T") (re.union (re.++ (str.to_re "u") (re.opt (str.to_re "e"))) (re.++ (str.to_re "h") (re.opt (str.to_re "u")) (re.opt (str.to_re "r")))) (re.opt (str.to_re ".")) (str.to_re "\u{a}")))) (re.union (re.++ (re.union (str.to_re "Sun") (str.to_re "Mom") (re.++ (str.to_re "S") (re.union (str.to_re "ues") (str.to_re "hurs"))) (str.to_re "Fri")) (re.opt (re.union (str.to_re "day") (str.to_re ".")))) (re.++ (str.to_re "Wed") (re.opt (re.union (str.to_re ".") (str.to_re "nesday")))) (re.++ (str.to_re "Sat") (re.opt (re.union (str.to_re ".") (str.to_re "urday")))) (re.++ (str.to_re "T") (re.union (re.++ (str.to_re "u") (re.opt (str.to_re "e"))) (re.++ (str.to_re "h") (re.opt (str.to_re "u")) (re.opt (str.to_re "r")))) (re.opt (str.to_re ".")) (str.to_re "\u{a}")))))))

(check-sat)
(exit)
