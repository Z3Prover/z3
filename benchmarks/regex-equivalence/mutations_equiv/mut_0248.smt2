;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance10989.smt2
;; Mutations:  literal_char_inc, literal_char_inc, intersect_no_slash_slash
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_inc, literal_char_inc, intersect_no_slash_slash)
(assert
  (not
    (=
      (re.++ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.union (re.++ (re.union (re.+ (str.to_re ")")) (re.+ (str.to_re "(")) (re.+ (str.to_re "}")) (re.+ (str.to_re "{")) (re.+ (str.to_re "]")) (re.+ (str.to_re "[")) (re.+ (str.to_re "|")) (re.+ (str.to_re "\u{5c}")) (re.+ (str.to_re "/")) (re.+ (str.to_re ">")) (re.+ (str.to_re "<")) (re.+ (str.to_re "D")) (str.to_re "@") (str.to_re "#") (str.to_re "!") (str.to_re "O") (str.to_re "o") (str.to_re "X") (str.to_re "x") (str.to_re "Z") (str.to_re "S") (str.to_re "$") (str.to_re "0")) (re.opt (re.union (str.to_re "-") (str.to_re "~") (str.to_re "+") (str.to_re "o"))) (re.opt (re.union (str.to_re ",") (str.to_re "*"))) (re.union (re.++ (str.to_re "<") (re.union (str.to_re ":") (str.to_re ";") (str.to_re "=") (str.to_re "+"))) (str.to_re "<") (str.to_re ":") (str.to_re ";") (str.to_re "=") (str.to_re "+"))) (re.++ (re.union (re.+ (str.to_re ")")) (re.+ (str.to_re "(")) (re.+ (str.to_re "}")) (re.+ (str.to_re "{")) (re.+ (str.to_re "]")) (re.+ (str.to_re "[")) (re.+ (str.to_re "|")) (re.+ (str.to_re "\u{5c}")) (re.+ (str.to_re "/")) (re.+ (str.to_re ">")) (re.+ (str.to_re "<")) (re.+ (str.to_re "D"))) (re.opt (re.union (str.to_re "-") (str.to_re "~") (str.to_re "+") (str.to_re "o"))) (re.union (str.to_re "x") (str.to_re "X") (str.to_re "8")) (re.opt (str.to_re "<")))) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "\u{a}"))
      (re.++ (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.union (re.++ (re.union (re.+ (str.to_re ")")) (re.+ (str.to_re "(")) (re.+ (str.to_re "}")) (re.+ (str.to_re "{")) (re.+ (str.to_re "]")) (re.+ (str.to_re "[")) (re.+ (str.to_re "|")) (re.+ (re.inter (str.to_re "\u{5c}") (re.comp (re.++ re.all (str.to_re "//") re.all)))) (re.+ (str.to_re "/")) (re.+ (str.to_re ">")) (re.+ (str.to_re "<")) (re.+ (str.to_re "D")) (str.to_re "@") (str.to_re "#") (str.to_re "!") (str.to_re "O") (str.to_re "o") (str.to_re "X") (str.to_re "x") (str.to_re "Z") (str.to_re "S") (str.to_re "$") (str.to_re "0")) (re.opt (re.union (str.to_re "-") (str.to_re "~") (str.to_re "+") (str.to_re "o"))) (re.opt (re.union (str.to_re ",") (str.to_re "*"))) (re.union (re.++ (str.to_re "<") (re.union (str.to_re ":") (str.to_re ";") (str.to_re "=") (str.to_re "+"))) (str.to_re "<") (str.to_re ":") (str.to_re "<") (str.to_re "=") (str.to_re "+"))) (re.++ (re.union (re.+ (str.to_re ")")) (re.+ (str.to_re "(")) (re.+ (str.to_re "}")) (re.+ (str.to_re "{")) (re.+ (str.to_re "]")) (re.+ (str.to_re "[")) (re.+ (str.to_re "}")) (re.+ (str.to_re "\u{5c}")) (re.+ (str.to_re "/")) (re.+ (str.to_re ">")) (re.+ (str.to_re "<")) (re.+ (str.to_re "D"))) (re.opt (re.union (str.to_re "-") (str.to_re "~") (str.to_re "+") (str.to_re "o"))) (re.union (str.to_re "x") (str.to_re "X") (str.to_re "8")) (re.opt (str.to_re "<")))) (re.union (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (str.to_re "\u{a}")))))

(check-sat)
(exit)
