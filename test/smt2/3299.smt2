(declare-fun a () Int)                                                          
(assert (distinct  "Good"  "Good"))                                             
(assert (> a 0 ))                                                               
(check-sat-using normalize-bounds)  