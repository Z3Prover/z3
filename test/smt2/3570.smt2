(set-option :trace true) 
(declare-fun a () Real)  
(assert (< (+ a) 8 a)) 
(check-sat-using qfnia) 