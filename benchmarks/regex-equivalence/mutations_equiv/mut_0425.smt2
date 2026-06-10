;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance06014.smt2
;; Mutations:  range_expand_hi, intersect_no_slash_slash, intersect_no_alnum5
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_expand_hi, intersect_no_slash_slash, intersect_no_alnum5)
(assert
  (not
    (=
      (re.union (re.++ (re.union (re.++ ((_ re.loop 3 3) (re.range "0" "9")) re.allchar ((_ re.loop 3 3) (re.range "0" "9")) re.allchar ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9"))) ((_ re.loop 11 11) (re.range "0" "9"))) (str.to_re "\u{a}")) (re.++ ((_ re.loop 2 2) (re.range "0" "9")) re.allchar ((_ re.loop 3 3) (re.range "0" "9")) re.allchar ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "/") ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9"))) ((_ re.loop 14 14) (re.range "0" "9")))
      (re.union (re.++ (re.union (re.++ (re.inter ((_ re.loop 3 3) (re.range "0" "9")) (re.comp (re.++ re.all ((_ re.loop 5 5) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) re.all))) re.allchar ((_ re.loop 3 3) (re.range "0" "9")) re.allchar ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9"))) ((_ re.loop 11 11) (re.range "0" "9"))) (str.to_re "\u{a}")) (re.++ ((_ re.loop 2 2) (re.range "0" "9")) re.allchar (re.inter ((_ re.loop 3 3) (re.range "0" "9")) (re.comp (re.++ re.all (str.to_re "//") re.all))) re.allchar ((_ re.loop 3 3) (re.range "0" ":")) (str.to_re "/") ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9"))) ((_ re.loop 14 14) (re.range "0" "9"))))))

(check-sat)
(exit)
