(set-option :nlsat.inline_vars true)
(assert (distinct (/ 40  (^ 0.375 210)) (^ 0 4.0)))
(check-sat)