;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11858.smt2
;; Mutations:  intersect_no_alnum3, union_to_inter
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_alnum3, union_to_inter)
(assert
  (not
    (=
      (re.++ (str.to_re "ShadowNet") (re.+ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (str.to_re "AID/User-Agent:Fen\u{ea}treEye/dss/cc.2_0_0.\u{a}"))
      (re.++ (str.to_re "ShadowNet") (re.+ (re.inter (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.inter (str.to_re "AID/User-Agent:Fen\u{ea}treEye/dss/cc.2_0_0.\u{a}") (re.comp (re.++ re.all ((_ re.loop 3 3) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) re.all)))))))

(check-sat)
(exit)
