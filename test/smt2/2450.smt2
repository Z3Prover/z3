(declare-fun a () Real) 
(declare-fun b () Real) 
(declare-fun c () Real) 
(declare-fun d () Real) 
(declare-fun e () Real) 
(declare-fun f () Real) 
(declare-fun g () Real)
(declare-fun j () Real) 
(declare-fun k () Real) 
(assert (or
    (not                  ;false
        (=>               
            (and            
                (= k 1.0)
                (= k 0.0) 
                (<= 1.0 f)) 
            (<= a (+ g b)))) 
    (and                    ; false
        (forall ((?d Real)) ;false
            (and                   
                (or                  
                    (<= 0.0 (+ (- b) ?d)) 
                    (= (- b f) 0.0))      
                (and 
                    (not (= d 0)) 
                    (not (= d 1.0)))))
        (and 
            (exists ((?h Real)) 
                (forall ((?d Real)) 
                    (exists ((?e Real)) 
                        (and 
                            (or 
                                (= j 0) 
                                (not (= (+ (- ?h) (- b f)) 0.0))) 
                            (or 
                                (and (< 0.0 ?h) (= ?e 0)) 
                                (or (<= (- b f) 0.0) (= (- b f) 0))) 
                            (and 
                                (<= 0.0 (+ ?e (* 2.0 ?d) (* (- 2.0) ?h))) 
                                (<= (+ ?d (* (- 2.0) ?h)) 0.00))))))
            (exists ((?h Real))
                (or 
                    (forall ((?e Real))
                        (or 
                            (<= ?h 0.0) 
                            (= (+ ?e f) 0.0)))
                    (and 
                        (or 
                            (not (= (+ (* (- 1.0) ?h) (* 2.0 j)) (- 1.0)))
                            (not (= (+ (* (- 2.0) ?h) (* (- 2.0) j)) 2.0)))
                        (forall ((?d Real)) 
                            (=  (* 2.0 ?d) ?h)))))))))
(assert (= b (+ j f)))  
(assert (= c (* e g)))  

(check-sat)
;(get-model)
