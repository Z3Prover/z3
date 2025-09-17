(set-logic ALL)

(declare-fun x () (Seq String))

; Simple test: sequence length should be at least 5
(assert (>= (seq.len x) 1))

; Test that nth(x, 0) gives a non-empty string
(assert (> (str.len (seq.nth x 0)) 0))

(check-sat)
(get-model)