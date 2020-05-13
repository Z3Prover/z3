(declare-fun X () String)  
(assert (not (str.in.re X (re.* (re.range "\x00" "\xFF")))))
(check-sat)
