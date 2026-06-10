;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance13239.smt2
;; Mutations:  intersect_no_upper2
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
;; R2: mutated (intersect_no_upper2)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "Host:") (re.range "0" "9") (str.to_re "toolbar.hotblox.com") (re.range "0" "9") (str.to_re "Host:http://mysearch.dropspam.com/index.php?tpid=\u{13}\u{a}")) (re.comp (re.++ (str.to_re "Host:") (re.range "0" "9") (re.inter (str.to_re "toolbar.hotblox.com") (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) (re.range "0" "9") (str.to_re "Host:http://mysearch.dropspam.com/index.php?tpid=\u{13}\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "Host:") (re.range "0" "9") (str.to_re "toolbar.hotblox.com") (re.range "0" "9") (str.to_re "Host:http://mysearch.dropspam.com/index.php?tpid=\u{13}\u{a}"))) (re.++ (str.to_re "Host:") (re.range "0" "9") (re.inter (str.to_re "toolbar.hotblox.com") (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) (re.range "0" "9") (str.to_re "Host:http://mysearch.dropspam.com/index.php?tpid=\u{13}\u{a}"))))))

(check-sat)
(exit)
