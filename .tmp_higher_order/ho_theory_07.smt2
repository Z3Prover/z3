; HO + Strings: predicate over strings
(set-logic HO_ALL)
(declare-fun is_prefix () (-> String String Bool))
(assert (= is_prefix (lambda ((p String) (s String)) (str.prefixof p s))))
(assert (not (is_prefix "he" "hello")))
(check-sat)
(exit)
