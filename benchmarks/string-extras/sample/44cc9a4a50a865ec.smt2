; origin: https://github.com/vlab-cs-ucsb/ABC/tree/master/test : benchmarks/appscan/cvc4/t01.smt2
(set-logic QF_S)
(set-option :produce-models true)

(declare-fun parameter () String)
(declare-fun a () String)
(declare-fun index () Int)
(declare-fun str1 () String)
(declare-fun index1 () Int)
(declare-fun sli () String)
(declare-fun index2 () Int)




(assert (= parameter "eOfferCode") )
(assert (= index (str.indexof a parameter 0) ) )

(assert (ite (not (= index (- 0 1) ) ) 
             (and (= str1 (str.substr a index (- (str.len a) index) ) ) 
                  (= index1 (str.indexof str1 "&" 0) )
                  (ite (= index1 (- 0 1) )
                       (and (= index2 (str.indexof str1 "=" 0) )
                            (= sli (str.substr str1 (+ index2 1) (- (str.len str1) (+ index2 1) ) ) )
                       )
                       (and (= index2 (str.indexof str1 "=" 0) )
                            (= sli (str.substr str1 (+ index2 1) (- index1 (+ index2 1) ) ) )
                       )
                  )
             )                 
             (= sli "")
        ) 
)

(assert (not (= sli "") ) )


(check-sat)

