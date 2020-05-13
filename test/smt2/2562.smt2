(set-option :model_validate true)
(declare-fun a () String)     
(declare-fun b () String)     
(declare-fun c () String)     
(assert (= (str.substr a 0 (str.len b)) ""))     
(assert (=      
            (ite      
                (= (str.len (str.substr (str.replace (str.replace a b "") "29M8u" "") 1 (- (str.len c) 1))) 0) 1 0
            )      
            0       
        )      
)     
(check-sat)   
