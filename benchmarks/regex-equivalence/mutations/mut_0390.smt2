;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance07727.smt2
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
    (re.union (re.inter (re.++ (re.opt (re.++ (str.to_re "http") (re.opt (str.to_re "s")) (str.to_re "://"))) (re.opt (str.to_re "www.")) (str.to_re "youtu") (re.opt (str.to_re "be")) (str.to_re ".") (re.+ (re.range "a" "z")) (str.to_re "/") (re.opt (re.++ (str.to_re "watch") (re.* re.allchar) (re.union (str.to_re "?") (str.to_re "&")) (str.to_re "v="))) (re.* re.allchar) (re.opt (re.++ (str.to_re "&") (re.* re.allchar))) (str.to_re "\u{a}")) (re.comp (re.++ (re.opt (re.++ (str.to_re "http") (re.opt (str.to_re "t")) (str.to_re "://"))) (re.opt (str.to_re "www.")) (str.to_re "youtu") (re.opt (str.to_re "be")) (str.to_re ".") (re.+ (re.range "a" "z")) (str.to_re "/") (re.opt (re.++ (str.to_re "watch") (re.* re.allchar) (re.union (str.to_re "?") (str.to_re "&")) (str.to_re "v="))) (re.* re.allchar) (re.opt (re.++ (str.to_re "&") (re.* re.allchar))) (str.to_re "\u{a}")))) (re.inter (re.comp (re.++ (re.opt (re.++ (str.to_re "http") (re.opt (str.to_re "s")) (str.to_re "://"))) (re.opt (str.to_re "www.")) (str.to_re "youtu") (re.opt (str.to_re "be")) (str.to_re ".") (re.+ (re.range "a" "z")) (str.to_re "/") (re.opt (re.++ (str.to_re "watch") (re.* re.allchar) (re.union (str.to_re "?") (str.to_re "&")) (str.to_re "v="))) (re.* re.allchar) (re.opt (re.++ (str.to_re "&") (re.* re.allchar))) (str.to_re "\u{a}"))) (re.++ (re.opt (re.++ (str.to_re "http") (re.opt (str.to_re "t")) (str.to_re "://"))) (re.opt (str.to_re "www.")) (str.to_re "youtu") (re.opt (str.to_re "be")) (str.to_re ".") (re.+ (re.range "a" "z")) (str.to_re "/") (re.opt (re.++ (str.to_re "watch") (re.* re.allchar) (re.union (str.to_re "?") (str.to_re "&")) (str.to_re "v="))) (re.* re.allchar) (re.opt (re.++ (str.to_re "&") (re.* re.allchar))) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
