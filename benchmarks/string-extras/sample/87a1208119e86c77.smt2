; origin: https://github.com/vlab-cs-ucsb/ABC/tree/master/test : benchmarks/appscan/cvc4/t07.smt2
(set-logic QF_S)
(set-option :produce-models true)


(declare-fun selKeyword_value () String)
(declare-fun selKeyword_value_trimed () String)
(declare-fun p1 () String)
(declare-fun p2 () String)
(declare-fun p3 () String)
(declare-fun url () String)
(declare-fun ret () String)
(declare-fun houseCityKeyName () String)


(assert (= selKeyword_value (str.++ p1 p2 p3) ) )

(assert (str.in_re  p1  (re.* (re.union (str.to_re " ") (str.to_re "\t") ) ) ) )

(assert (str.in_re  p3  (re.* (re.union (str.to_re " ") (str.to_re "\t") ) ) ) )

(assert (not (str.suffixof " " p2) ) )

(assert (not (str.suffixof "\t" p2) ) )

(assert (not (str.prefixof "\t" p2) ) )

(assert (not (str.prefixof " " p2) ) )

(assert (= selKeyword_value_trimed p2) )

(assert (= url (str.++  "http://xf.house.somesite.com/"  houseCityKeyName  "/search/0-0-0-0-0-0-0-0-0-1-1.html") ) )

(assert (ite (not (= "" selKeyword_value_trimed ) )
             (= ret (str.++  url  "?keyword="  selKeyword_value_trimed) )
             (= ret url)
        ) 
)


(check-sat)

