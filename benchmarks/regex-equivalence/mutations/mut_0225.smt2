;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance03702.smt2
;; Mutations:  literal_char_inc
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
;; R2: mutated (literal_char_inc)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.union (re.range "A" "Z") (re.range "a" "z")) (str.to_re ":\u{5c}") (re.* (re.++ (re.union (str.to_re "\u{22}") (str.to_re "*") (str.to_re "/") (str.to_re ":") (str.to_re "?") (str.to_re "|") (str.to_re "<") (str.to_re ">") (str.to_re "\u{5c}") (str.to_re ".") (re.range "\u{0}" " ")) (re.opt (re.++ (re.* (re.union (str.to_re "\u{22}") (str.to_re "*") (str.to_re "/") (str.to_re ":") (str.to_re "?") (str.to_re "|") (str.to_re "<") (str.to_re ">") (str.to_re "\u{5c}") (re.range "\u{0}" "\u{1f}"))) (re.union (str.to_re "\u{22}") (str.to_re "*") (str.to_re "/") (str.to_re ":") (str.to_re "?") (str.to_re "|") (str.to_re "<") (str.to_re ">") (str.to_re "\u{5c}") (str.to_re ".") (re.range "\u{0}" " ")))) (str.to_re "\u{5c}"))) (str.to_re "\u{a}")) (re.comp (re.++ (re.union (re.range "A" "Z") (re.range "a" "z")) (str.to_re ":\u{5c}") (re.* (re.++ (re.union (str.to_re "\u{22}") (str.to_re "*") (str.to_re "/") (str.to_re ":") (str.to_re "?") (str.to_re "|") (str.to_re "<") (str.to_re ">") (str.to_re "\u{5c}") (str.to_re ".") (re.range "\u{0}" " ")) (re.opt (re.++ (re.* (re.union (str.to_re "\u{22}") (str.to_re "*") (str.to_re "/") (str.to_re ":") (str.to_re "?") (str.to_re "}") (str.to_re "<") (str.to_re ">") (str.to_re "\u{5c}") (re.range "\u{0}" "\u{1f}"))) (re.union (str.to_re "\u{22}") (str.to_re "*") (str.to_re "/") (str.to_re ":") (str.to_re "?") (str.to_re "|") (str.to_re "<") (str.to_re ">") (str.to_re "\u{5c}") (str.to_re ".") (re.range "\u{0}" " ")))) (str.to_re "\u{5c}"))) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.union (re.range "A" "Z") (re.range "a" "z")) (str.to_re ":\u{5c}") (re.* (re.++ (re.union (str.to_re "\u{22}") (str.to_re "*") (str.to_re "/") (str.to_re ":") (str.to_re "?") (str.to_re "|") (str.to_re "<") (str.to_re ">") (str.to_re "\u{5c}") (str.to_re ".") (re.range "\u{0}" " ")) (re.opt (re.++ (re.* (re.union (str.to_re "\u{22}") (str.to_re "*") (str.to_re "/") (str.to_re ":") (str.to_re "?") (str.to_re "|") (str.to_re "<") (str.to_re ">") (str.to_re "\u{5c}") (re.range "\u{0}" "\u{1f}"))) (re.union (str.to_re "\u{22}") (str.to_re "*") (str.to_re "/") (str.to_re ":") (str.to_re "?") (str.to_re "|") (str.to_re "<") (str.to_re ">") (str.to_re "\u{5c}") (str.to_re ".") (re.range "\u{0}" " ")))) (str.to_re "\u{5c}"))) (str.to_re "\u{a}"))) (re.++ (re.union (re.range "A" "Z") (re.range "a" "z")) (str.to_re ":\u{5c}") (re.* (re.++ (re.union (str.to_re "\u{22}") (str.to_re "*") (str.to_re "/") (str.to_re ":") (str.to_re "?") (str.to_re "|") (str.to_re "<") (str.to_re ">") (str.to_re "\u{5c}") (str.to_re ".") (re.range "\u{0}" " ")) (re.opt (re.++ (re.* (re.union (str.to_re "\u{22}") (str.to_re "*") (str.to_re "/") (str.to_re ":") (str.to_re "?") (str.to_re "}") (str.to_re "<") (str.to_re ">") (str.to_re "\u{5c}") (re.range "\u{0}" "\u{1f}"))) (re.union (str.to_re "\u{22}") (str.to_re "*") (str.to_re "/") (str.to_re ":") (str.to_re "?") (str.to_re "|") (str.to_re "<") (str.to_re ">") (str.to_re "\u{5c}") (str.to_re ".") (re.range "\u{0}" " ")))) (str.to_re "\u{5c}"))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
