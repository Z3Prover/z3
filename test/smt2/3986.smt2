(set-logic NRA)
(assert (! (distinct 0.0 8.0 8.0 0.6 837.0) :named IP_12))
(reset-assertions)
(check-sat)
(assert (! (exists ((q4 Real)) (distinct q4 72.0)) :named IP_13))