; origin: https://github.com/vlab-cs-ucsb/ABC/tree/master/test : benchmarks/appscan/cvc4/t03.smt2
(set-logic QF_S)
(set-option :produce-models true)

(declare-fun cookie () String)
(declare-fun cookie_part1 () String)
(declare-fun cookie_part2 () String)
(declare-fun cookie_part3 () String)
(declare-fun l1 () String)

(assert (= cookie  (str.++ cookie_part1 cookie_part2 cookie_part3) ) ) 

(assert (str.in_re cookie_part2 (re.++ (re.union (str.to_re "?") (str.to_re ";") ) 
                                       (str.to_re "searchLang=")
                                       (re.* (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c") (str.to_re "d") (str.to_re "e") (str.to_re "f") (str.to_re "g") (str.to_re "h") (str.to_re "i") (str.to_re "j") (str.to_re "k") (str.to_re "l") (str.to_re "m") (str.to_re "n") ) )
                                )
        )
)

(assert (=> (not (= "" cookie_part3) ) (= cookie_part3 (str.++ ";" l1) ) ) )

(assert (> (str.len cookie_part2) 11) )

(assert (= cookie "expires=Thu, 18 Dec 2013 12:00:00 UTC;searchLang=nb;domain=local;") )


(check-sat)


