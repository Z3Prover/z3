;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11761.smt2
;; Mutations:  literal_char_dec, literal_char_inc, literal_char_inc
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
;; R2: mutated (literal_char_dec, literal_char_inc, literal_char_inc)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.union (str.to_re "~") (str.to_re "`") (str.to_re "!") (str.to_re "@") (str.to_re "#") (str.to_re "$") (str.to_re "%") (str.to_re "^") (str.to_re "&") (str.to_re "*") (str.to_re "(") (str.to_re ")") (str.to_re "-") (str.to_re "_") (str.to_re "=") (str.to_re "+") (str.to_re "\u{5c}") (str.to_re "|") (str.to_re "[") (str.to_re "]") (str.to_re "{") (str.to_re "}") (str.to_re ";") (str.to_re ":") (str.to_re "\u{22}") (str.to_re "'") (str.to_re ",") (str.to_re "<") (str.to_re ".") (str.to_re "/") (str.to_re ">") (str.to_re "?") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.* (re.++ (re.* (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) (re.opt (re.union (str.to_re "-") (str.to_re "_") (str.to_re ".") (str.to_re "/"))) (re.+ (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))))) (str.to_re "\u{a}")) (re.comp (re.++ (re.union (str.to_re "~") (str.to_re "a") (str.to_re "!") (str.to_re "@") (str.to_re "#") (str.to_re "$") (str.to_re "%") (str.to_re "_") (str.to_re "&") (str.to_re "*") (str.to_re "(") (str.to_re ")") (str.to_re "-") (str.to_re "_") (str.to_re "=") (str.to_re "+") (str.to_re "\u{5c}") (str.to_re "|") (str.to_re "[") (str.to_re "]") (str.to_re "{") (str.to_re "}") (str.to_re ";") (str.to_re ":") (str.to_re "\u{22}") (str.to_re "'") (str.to_re ",") (str.to_re "<") (str.to_re ".") (str.to_re "/") (str.to_re ">") (str.to_re "?") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.* (re.++ (re.* (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) (re.opt (re.union (str.to_re "-") (str.to_re "_") (str.to_re "-") (str.to_re "/"))) (re.+ (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))))) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.union (str.to_re "~") (str.to_re "`") (str.to_re "!") (str.to_re "@") (str.to_re "#") (str.to_re "$") (str.to_re "%") (str.to_re "^") (str.to_re "&") (str.to_re "*") (str.to_re "(") (str.to_re ")") (str.to_re "-") (str.to_re "_") (str.to_re "=") (str.to_re "+") (str.to_re "\u{5c}") (str.to_re "|") (str.to_re "[") (str.to_re "]") (str.to_re "{") (str.to_re "}") (str.to_re ";") (str.to_re ":") (str.to_re "\u{22}") (str.to_re "'") (str.to_re ",") (str.to_re "<") (str.to_re ".") (str.to_re "/") (str.to_re ">") (str.to_re "?") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.* (re.++ (re.* (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) (re.opt (re.union (str.to_re "-") (str.to_re "_") (str.to_re ".") (str.to_re "/"))) (re.+ (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))))) (str.to_re "\u{a}"))) (re.++ (re.union (str.to_re "~") (str.to_re "a") (str.to_re "!") (str.to_re "@") (str.to_re "#") (str.to_re "$") (str.to_re "%") (str.to_re "_") (str.to_re "&") (str.to_re "*") (str.to_re "(") (str.to_re ")") (str.to_re "-") (str.to_re "_") (str.to_re "=") (str.to_re "+") (str.to_re "\u{5c}") (str.to_re "|") (str.to_re "[") (str.to_re "]") (str.to_re "{") (str.to_re "}") (str.to_re ";") (str.to_re ":") (str.to_re "\u{22}") (str.to_re "'") (str.to_re ",") (str.to_re "<") (str.to_re ".") (str.to_re "/") (str.to_re ">") (str.to_re "?") (str.to_re " ") (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}") (str.to_re "\u{d}")) (re.* (re.++ (re.* (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) (re.opt (re.union (str.to_re "-") (str.to_re "_") (str.to_re "-") (str.to_re "/"))) (re.+ (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
