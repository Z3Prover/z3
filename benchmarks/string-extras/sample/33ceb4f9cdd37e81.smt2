; origin: https://github.com/vlab-cs-ucsb/ABC/tree/master/test : benchmarks/pisa/cvc4/pisa-007.smt2
(set-logic QF_S)
(set-option :produce-models true)


(declare-fun s  () String)
(declare-fun filename_0  () String)
(declare-fun filename_1  () String)
(declare-fun filename_2  () String)
(declare-fun i0 () Int)
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun i3 () Int)
(declare-fun tmpStr0 () String)
(declare-fun tmpStr1 () String)
(declare-fun tmpStr2 () String)


(assert (= filename_0 s) )

(assert (= i0 (str.indexof filename_0 "/" 0) ) )

(assert (ite (not (= i0 (- 0 1) ) )
             (and (ite (str.contains filename_0 "/")
                       (and (= filename_0 (str.++ tmpStr0 (str.++ "/" tmpStr1) ) )
                            (not (str.contains tmpStr1 "/") )
                            (= i1 (str.len tmpStr0) )             
                       )
                       (= i1 (- 0 1) )
                  )                  
                  (= i2 (- (str.len filename_0) i1) )
                  (= filename_1 (str.substr filename_0 i1 i2) )
             )
             (= filename_1 filename_0)
        )
)


(assert (= i3 (str.indexof filename_1 "." 0) ) )


(assert (ite (not (= i3 (- 0 1) ) )
             (= filename_2 (str.substr filename_1 0 i3) )
             (= filename_2 filename_1)
        ) 
)

(assert (str.contains filename_2 "../") )


(check-sat)

