;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance12733.smt2
;; Mutations:  bound_lower_dec, range_shrink_hi
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
;; R2: mutated (bound_lower_dec, range_shrink_hi)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "\u{a}\u{22}http://video.google.com/googleplayer.swf?docId=") ((_ re.loop 19 19) (re.range "0" "9")) (str.to_re "&hl=") ((_ re.loop 2 2) (re.range "a" "z")) (str.to_re "\u{22}")) (re.comp (re.++ (str.to_re "\u{a}\u{22}http://video.google.com/googleplayer.swf?docId=") ((_ re.loop 19 19) (re.range "0" "8")) (str.to_re "&hl=") ((_ re.loop 1 2) (re.range "a" "z")) (str.to_re "\u{22}")))) (re.inter (re.comp (re.++ (str.to_re "\u{a}\u{22}http://video.google.com/googleplayer.swf?docId=") ((_ re.loop 19 19) (re.range "0" "9")) (str.to_re "&hl=") ((_ re.loop 2 2) (re.range "a" "z")) (str.to_re "\u{22}"))) (re.++ (str.to_re "\u{a}\u{22}http://video.google.com/googleplayer.swf?docId=") ((_ re.loop 19 19) (re.range "0" "8")) (str.to_re "&hl=") ((_ re.loop 1 2) (re.range "a" "z")) (str.to_re "\u{22}"))))))

(check-sat)
(exit)
