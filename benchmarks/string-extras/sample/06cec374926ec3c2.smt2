; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : parikh-constraints.smt2
;(set-logic ALL)
;(set-option :strings-exp true)
;(set-option :produce-models true)
;(set-option :rewrite-divk true)

(declare-fun value2 () String)
(declare-fun key2 () String)

(assert 

    (str.contains
            (str.replace
                   (str.substr
                            value2
                          0 (+ (str.indexof value2 "G" 0) 1))
                     "G" "g")
     "M")

 )

(check-sat)

;(get-value (value2))
;(get-value (key2))