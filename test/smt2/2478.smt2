(declare-fun a () String)  
(declare-fun b () String) 
(declare-fun c () String) 
(declare-fun d () String)  
(declare-fun shifted1_value1 () String) 
(declare-fun f () String)   
(declare-fun g () String) 


(assert 
    (and 
        (not (str.contains (str.substr c 0 (str.len f)) "G")) 
        (not (str.contains (str.substr c 0 (str.len f)) "F")) 
    )
)

(assert (not (str.contains f "H")))

(assert (= d "cachecontrol"))
(assert 
    (and 
        (not (str.contains f "E")) 
        (not (str.contains f "D")) 
        (not (str.contains f "C"))
    )
)
(assert 
    (and 
        (not (str.contains (str.substr c 0 (str.len f)) "A")) 
        (not (= (str.at (str.substr c 0 (str.len f)) (- (str.len f) 1)) "\v"))
    )
)
(assert (not (= (str.at f (- (str.len f) 1)) "\r")))
(assert 
    (and 
        (not (= (str.at (str.substr c 0 (str.len f)) (- (str.len (str.substr c 0 (str.len f))) 1)) "\n"))
        (not (= (str.at (str.substr c 0 (str.len f)) (- (str.len f) 1)) "\t")) 
        (not (= (str.at (str.substr c 0 (str.len f)) (- (str.len f) 1)) " "))
    )
)         
(assert (not (= (str.at f 0) "\f")))
(assert 
    (and   
        (not (= (str.at (str.substr c 0 (str.len f)) 0) "\v")) 
        (not (= (str.at (str.substr c 0 (str.len f)) 0) "\r"))
    )
)
(assert 
    (and 
        (not (= (str.at (str.substr c 0 (str.len f)) 0) "\v")) 
        (not (= (str.at (str.substr c 0 (str.len f)) 0) "\r")) 
    )
)
(assert 
    (and 
        (not (= (str.at f 0) "\n")) 
        (not (= (str.at f 0) "\t"))
        (= (str.indexof f "=" 0) (- 1)) 
        (not (= (str.len f) 0)) 
    )
)
(assert
    (and
        (not (= ( str.at (str.substr c 0 (str.len f)) 0) " "))
        (= ( str.indexof (str.substr c 0  (str.len f)) "=" 0) (- 1)) 
    )
)

(assert (not (str.contains f ",")))

(assert 
(<= 0 (+ (str.indexof (str.substr shifted1_value1 0 (str.indexof (str.substr b 0 (str.len shifted1_value1)) "=" 0)) "N" 0) 1))  
)
(assert 
    (<= 0 (- (str.len ( str.substr (str.substr b 0 (str.len shifted1_value1)) 0 (- ( str.indexof shifted1_value1 "=" 0) 0))) (+ ( str.indexof ( str.substr (str.substr b 0 (str.len shifted1_value1)) 0 (- ( str.indexof shifted1_value1 "=" 0) 0)) "N" 0) 1))) 
)
(assert 
    (<= 0 (- (+ ( str.indexof ( str.substr (str.substr b 0 (str.len shifted1_value1)) 0  ( str.indexof (str.substr b 0 (str.len shifted1_value1)) "=" 0)) "N" 0) 1)))
)
(assert 
    (<= 0 (+ ( str.indexof ( str.substr (str.substr b 0 (str.len shifted1_value1)) 0 (- ( str.indexof shifted1_value1 "=" 0) 0)) "N" 0) 1)) 
)
(assert 
(<= 0 (- (str.len ( str.substr shifted1_value1 0 (- ( str.indexof (str.substr b 0 (str.len shifted1_value1)) "=" 0) 0))) (+ ( str.indexof ( str.substr shifted1_value1 0 (- (str.indexof (str.substr b 0 (str.len shifted1_value1)) "=" 0) 0)) "N" 0) 1))) 
)
(assert 
(<= 0 (- (str.len ( str.substr shifted1_value1 0 (- ( str.indexof (str.substr b 0 (str.len shifted1_value1)) "=" 0) 0))) (+ ( str.indexof ( str.substr shifted1_value1 0 (- (str.indexof (str.substr b 0 (str.len shifted1_value1)) "=" 0) 0)) "N" 0) 1))) 
)
(assert
(<= 0 (- (str.len ( str.substr shifted1_value1 0 (- ( str.indexof shifted1_value1 "=" 0) 0))) (+ ( str.indexof ( str.substr shifted1_value1 0 (- ( str.indexof shifted1_value1 "=" 0) 0)) "N" 0) 1)))  
)
(assert (<= 0 (str.indexof (str.substr b 0 (str.len shifted1_value1)) "=" 0)))
(assert (<= 0 (- (str.indexof shifted1_value1 "=" 0))))
(assert (<= 0 (+ (str.indexof (str.substr b 0 (str.len shifted1_value1)) "=" 0) 1)))
(assert (<= 0 (- (str.len (str.substr b 0 (str.len shifted1_value1)))  (+ ( str.indexof shifted1_value1 "=" 0) 1))) )
(assert (<= 0 (-  (+ ( str.indexof (str.substr c 0 (str.len f)) "S" 0) 1))))
(assert (<= 0 (- (str.len f) (+ ( str.indexof f "S" 0) 1))))
(assert (<= 0 (- (str.len (str.substr c 0 (str.len f))) (+ ( str.indexof (str.substr c 0 (str.len f)) "S" 0) 1))))
(assert (<= 0  (+ ( str.indexof f "S" 0) 1)))
(assert (<= 0 (+ (str.indexof (str.substr c 0 (str.len f)) "S" 0) 1)))
(assert (<= 0 (- (str.len (str.substr c 0 (str.len f))) (+ ( str.indexof f "S" 0) 1))))  
(assert (= (not (= "" g)) true (= (str.replace (str.replace a d "") "Pkgwt" "") "Example:"))) 
(assert (= a (str.++ (str.++ d "Pkgwt") g))) 
(assert (= b (str.++ shifted1_value1 g))) 
(assert (= c (str.++ f g))) 
(check-sat)