(set-option :smt.theory_case_split true)
(declare-fun value2 () String)
(assert (not (= (ite (str.contains (str.++ (str.replace (str.substr
 (str.substr value2 0 (- (- (str.len value2)))) 0 (- (+ (str.indexof
 (str.substr value2 0 (- (- (str.len value2) 1) 0)) "P" 0) 1) 0)) "P"
 "p")) "Z") 1 0) 0)))
 (check-sat)