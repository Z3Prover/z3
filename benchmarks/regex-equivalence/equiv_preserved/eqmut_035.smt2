;; Equivalence-Preserving Mutation Benchmark
;; Base: http_request
;; Transforms: union_assoc, union_assoc, double_comp, inter_idemp, absorb_empty
;; Status: unsat
;;
;; R1 (original) and R2 (transformed) are language-equivalent.
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "equiv_preserved")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ (re.++ (re.++ (re.++ (re.union (re.union (re.union (re.union (str.to_re "GET") (str.to_re "POST")) (str.to_re "PUT")) (str.to_re "DELETE")) (str.to_re "HEAD")) (str.to_re " /")) (re.* (re.union (re.union (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "/")) (str.to_re "-")) (str.to_re "_")) (str.to_re ".")))) (str.to_re " HTTP/1.")) (re.union (str.to_re "0") (str.to_re "1"))) (re.++ (re.++ (re.++ (re.++ (re.union (re.union (re.inter (re.union (re.comp (re.comp (re.union (str.to_re "GET") (str.to_re "POST")))) (str.to_re "PUT")) (re.union (re.comp (re.comp (re.union (str.to_re "GET") (str.to_re "POST")))) (str.to_re "PUT"))) (str.to_re "DELETE")) (str.to_re "HEAD")) (str.to_re " /")) (re.* (re.union (re.union (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")) (str.to_re "/")) (re.union (str.to_re "-") (re.union (str.to_re "_") (str.to_re ".")))))) (str.to_re " HTTP/1.")) (re.union (str.to_re "0") (re.union (str.to_re "1") re.none))))))

(check-sat)
(exit)
