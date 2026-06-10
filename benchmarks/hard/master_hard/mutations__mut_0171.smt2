;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00402.smt2
;; Mutations:  bound_lower_dec, literal_char_inc, intersect_no_slash_slash
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
;; R2: mutated (bound_lower_dec, literal_char_inc, intersect_no_slash_slash)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.* (str.to_re " ")) (re.opt (str.to_re ")")) (re.opt (re.union re.allchar (str.to_re "-") (str.to_re "_ "))) (re.opt (str.to_re "(")) ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re ")")) (re.opt (re.union re.allchar (str.to_re "-") (str.to_re "_ "))) (re.opt (str.to_re "(")) ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re ")")) (re.opt (re.union re.allchar (str.to_re "-") (str.to_re "_ "))) (re.opt (str.to_re "(")) ((_ re.loop 4 4) (re.range "0" "9")) (re.opt (str.to_re ")")) (re.* (str.to_re " ")) (str.to_re "\u{a}") (re.opt (str.to_re "+")) (re.opt (str.to_re " ")) (re.opt (str.to_re "(")) (re.opt (str.to_re " ")) (re.opt ((_ re.loop 1 3) (re.range "0" "9")))) (re.comp (re.++ (re.* (str.to_re " ")) (re.opt (str.to_re ")")) (re.opt (re.inter (re.union re.allchar (str.to_re "-") (str.to_re "_ ")) (re.comp (re.++ re.all (str.to_re "//") re.all)))) (re.opt (str.to_re "(")) ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re ")")) (re.opt (re.union re.allchar (str.to_re "-") (str.to_re "_ "))) (re.opt (str.to_re "(")) ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re ")")) (re.opt (re.union re.allchar (str.to_re ".") (str.to_re "_ "))) (re.opt (str.to_re "(")) ((_ re.loop 4 4) (re.range "0" "9")) (re.opt (str.to_re ")")) (re.* (str.to_re " ")) (str.to_re "\u{a}") (re.opt (str.to_re "+")) (re.opt (str.to_re " ")) (re.opt (str.to_re "(")) (re.opt (str.to_re " ")) (re.opt ((_ re.loop 0 3) (re.range "0" "9")))))) (re.inter (re.comp (re.++ (re.* (str.to_re " ")) (re.opt (str.to_re ")")) (re.opt (re.union re.allchar (str.to_re "-") (str.to_re "_ "))) (re.opt (str.to_re "(")) ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re ")")) (re.opt (re.union re.allchar (str.to_re "-") (str.to_re "_ "))) (re.opt (str.to_re "(")) ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re ")")) (re.opt (re.union re.allchar (str.to_re "-") (str.to_re "_ "))) (re.opt (str.to_re "(")) ((_ re.loop 4 4) (re.range "0" "9")) (re.opt (str.to_re ")")) (re.* (str.to_re " ")) (str.to_re "\u{a}") (re.opt (str.to_re "+")) (re.opt (str.to_re " ")) (re.opt (str.to_re "(")) (re.opt (str.to_re " ")) (re.opt ((_ re.loop 1 3) (re.range "0" "9"))))) (re.++ (re.* (str.to_re " ")) (re.opt (str.to_re ")")) (re.opt (re.inter (re.union re.allchar (str.to_re "-") (str.to_re "_ ")) (re.comp (re.++ re.all (str.to_re "//") re.all)))) (re.opt (str.to_re "(")) ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re ")")) (re.opt (re.union re.allchar (str.to_re "-") (str.to_re "_ "))) (re.opt (str.to_re "(")) ((_ re.loop 3 3) (re.range "0" "9")) (re.opt (str.to_re ")")) (re.opt (re.union re.allchar (str.to_re ".") (str.to_re "_ "))) (re.opt (str.to_re "(")) ((_ re.loop 4 4) (re.range "0" "9")) (re.opt (str.to_re ")")) (re.* (str.to_re " ")) (str.to_re "\u{a}") (re.opt (str.to_re "+")) (re.opt (str.to_re " ")) (re.opt (str.to_re "(")) (re.opt (str.to_re " ")) (re.opt ((_ re.loop 0 3) (re.range "0" "9"))))))))

(check-sat)
(exit)
