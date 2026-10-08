; strtol clamped this unsigned seed to INT_MAX on Windows.
(set-option :smt.random_seed 4294967295)
(get-option :smt.random_seed)
(check-sat)
