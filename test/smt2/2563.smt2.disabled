(declare-fun a () String)                                                       
(declare-fun b () String)                                                       
(declare-fun c () String)                                                       
(assert                                                                         
  (not                                                                          
    (= (str.substr a 0 (str.len b)) "")                                         
  )                                                                             
)                                                                               
(assert                                                                         
  (and                                                                          
    (=                                                                          
      (ite                                                                      
        (=                                                                      
          (str.len                                                              
            (str.substr (str.replace (str.replace a b "") "29M8u" "") 1 (- (str.len c) 1))
          )                                                                     
          0                                                                     
        )                                                                       
        1                                                                       
        0                                                                       
      )                                                                         
      (ite                                                                      
        (=                                                                      
          (str.at (str.replace (str.replace a b "") "29M8u" "") 0)              
          ""                                                                    
        )                                                                       
        1                                                                       
        0                                                                       
      )                                                                         
      (ite                                                                      
        (=                                                                      
          (str.len (str.replace (str.replace a b "") "29M8u" ""))               
          0                                                                     
        )                                                                       
        1                                                                       
        0                                                                       
      )                                                                         
      0                                                                         
    )                                                                           
    (>=                                                                         
      (-                                                                        
        (str.len (str.replace (str.replace a b "") "29M8u" ""))                 
        1                                                                       
      )                                                                         
      0                                                                         
    )                                                                           
  )                                                                             
)                                                                               
(check-sat)