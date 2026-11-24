; origin: https://github.com/vlab-cs-ucsb/ABC/tree/master/test : benchmarks/appscan/cvc4/t06.smt2
(set-logic QF_S)
(set-option :produce-models true)


(declare-fun src () String)
(declare-fun URL () String)
(declare-fun ret () String)
(declare-fun pred () Bool)
(declare-fun p1 () Bool)


(assert (= p1 (str.suffixof  "_hA"  src) ) )

(assert (= pred  (or (str.suffixof  "_ha"  src) (str.suffixof "_Ha"  src) (str.suffixof "_HA"  src) p1 ) ) )

(assert (ite (not (= src "") ) 
             (ite pred
                  (= ret src)
                  (= ret (str.++ src "_ha") )
             )     
             (ite (> (str.indexof URL "www.ha45.com/index.html" 0) (- 0 1) )
                  (= ret "srcindex_ha")
                  (ite (> (str.indexof URL "www.ha45.com/index.htm" 0) (- 0 1) )
                       (= ret "srcieak_ha")
                       (ite (> (str.indexof URL "www.ha45.com/?vit=fws" 0) (- 0 1) )
                            (= ret "srcvit_ha")
                            (= ret "siteha45")
                       )
                  )
            )
       )
)

(assert (str.suffixof "_ha" ret) )
(assert (not (= src "") ) )


(check-sat)

