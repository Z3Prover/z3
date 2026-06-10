;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance07417.smt2
;; Mutations:  range_shrink_hi, range_shrink_hi
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_hi, range_shrink_hi)
(assert
  (not
    (=
      (re.++ (str.to_re "sips:") (re.* re.allchar) (str.to_re "@") (re.union (re.++ ((_ re.loop 1 3) (re.range "0" "9")) re.allchar ((_ re.loop 1 3) (re.range "0" "9")) re.allchar ((_ re.loop 1 3) (re.range "0" "9")) re.allchar ((_ re.loop 1 3) (re.range "0" "9"))) (re.++ (re.+ (re.union (re.range "a" "z") (re.range "A" "Z") (str.to_re "-") (str.to_re "."))) (str.to_re ".") ((_ re.loop 2 5) (re.union (re.range "a" "z") (re.range "A" "Z"))))) (re.opt (re.++ (str.to_re ":") ((_ re.loop 1 5) (re.range "0" "9")))) (re.opt (re.+ (re.union (str.to_re "-") (str.to_re "?") (str.to_re "@") (str.to_re ";") (str.to_re ",") (str.to_re "=") (str.to_re "%") (str.to_re "&") (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_")))) (str.to_re "\u{a}"))
      (re.++ (str.to_re "sips:") (re.* re.allchar) (str.to_re "@") (re.union (re.++ ((_ re.loop 1 3) (re.range "0" "9")) re.allchar ((_ re.loop 1 3) (re.range "0" "9")) re.allchar ((_ re.loop 1 3) (re.range "0" "8")) re.allchar ((_ re.loop 1 3) (re.range "0" "8"))) (re.++ (re.+ (re.union (re.range "a" "z") (re.range "A" "Z") (str.to_re "-") (str.to_re "."))) (str.to_re ".") ((_ re.loop 2 5) (re.union (re.range "a" "z") (re.range "A" "Z"))))) (re.opt (re.++ (str.to_re ":") ((_ re.loop 1 5) (re.range "0" "9")))) (re.opt (re.+ (re.union (str.to_re "-") (str.to_re "?") (str.to_re "@") (str.to_re ";") (str.to_re ",") (str.to_re "=") (str.to_re "%") (str.to_re "&") (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_")))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
