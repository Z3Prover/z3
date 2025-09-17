(set-logic ALL)

(declare-fun x () (Seq String))

(define-fun-rec f ((s (Seq String))) String
    (ite (= (seq.len s) 0)
    	 ""
	 (str.++ (seq.nth s 0) (f (seq.extract s 1 (- (seq.len s) 1))))))

(assert (>= (str.len (f x)) 5))
(check-sat)
(get-model)