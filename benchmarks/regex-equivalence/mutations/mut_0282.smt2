;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance12186.smt2
;; Mutations:  plus_to_star, intersect_no_dot_dot
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
;; R2: mutated (plus_to_star, intersect_no_dot_dot)
(assert
  (str.in_re x
    (re.union (re.inter (re.union (re.++ (str.to_re "<") (re.union (re.++ (str.to_re "!--") (re.* re.allchar)) (str.to_re "script")) (re.* (re.union re.allchar (re.++ (str.to_re "\u{a}") (re.comp (str.to_re "<"))))) (re.union (str.to_re "--") (str.to_re "script")) (str.to_re ">")) (re.++ (str.to_re "<") (re.opt (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.* (re.comp (str.to_re "<"))) (str.to_re ">") (re.opt (str.to_re "/")) (re.+ (re.union (str.to_re "!") (str.to_re "?") (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_")))) (re.++ (str.to_re "\u{a}&") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re ";"))) (re.comp (re.union (re.++ (str.to_re "<") (re.union (re.++ (str.to_re "!--") (re.* re.allchar)) (str.to_re "script")) (re.* (re.union re.allchar (re.++ (str.to_re "\u{a}") (re.comp (str.to_re "<"))))) (re.union (str.to_re "--") (str.to_re "script")) (str.to_re ">")) (re.++ (str.to_re "<") (re.opt (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.* (re.comp (str.to_re "<"))) (str.to_re ">") (re.opt (str.to_re "/")) (re.+ (re.union (str.to_re "!") (str.to_re "?") (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_")))) (re.++ (re.inter (str.to_re "\u{a}&") (re.comp (re.++ re.all (str.to_re "..") re.all))) (re.* (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re ";"))))) (re.inter (re.comp (re.union (re.++ (str.to_re "<") (re.union (re.++ (str.to_re "!--") (re.* re.allchar)) (str.to_re "script")) (re.* (re.union re.allchar (re.++ (str.to_re "\u{a}") (re.comp (str.to_re "<"))))) (re.union (str.to_re "--") (str.to_re "script")) (str.to_re ">")) (re.++ (str.to_re "<") (re.opt (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.* (re.comp (str.to_re "<"))) (str.to_re ">") (re.opt (str.to_re "/")) (re.+ (re.union (str.to_re "!") (str.to_re "?") (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_")))) (re.++ (str.to_re "\u{a}&") (re.+ (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re ";")))) (re.union (re.++ (str.to_re "<") (re.union (re.++ (str.to_re "!--") (re.* re.allchar)) (str.to_re "script")) (re.* (re.union re.allchar (re.++ (str.to_re "\u{a}") (re.comp (str.to_re "<"))))) (re.union (str.to_re "--") (str.to_re "script")) (str.to_re ">")) (re.++ (str.to_re "<") (re.opt (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}"))) (re.* (re.comp (str.to_re "<"))) (str.to_re ">") (re.opt (str.to_re "/")) (re.+ (re.union (str.to_re "!") (str.to_re "?") (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_")))) (re.++ (re.inter (str.to_re "\u{a}&") (re.comp (re.++ re.all (str.to_re "..") re.all))) (re.* (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "_"))) (str.to_re ";")))))))

(check-sat)
(exit)
