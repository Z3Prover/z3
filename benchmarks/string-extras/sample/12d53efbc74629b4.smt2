; origin: https://github.com/vlab-cs-ucsb/ABC/tree/master/test : fixtures/old_tests/nullhttpd.smt2
(set-logic QF_S)

(declare-fun a1 () String)
(declare-fun a2 () String)
(declare-fun a () String)
(declare-fun c () String)
(declare-fun d1 () String)
(declare-fun d () String)
(declare-fun b () String)
(declare-fun var_S () String)

(assert (= a1 "POST"))
(assert (= a (str.++ a1 a2)))
(assert (= c "content-length:a-800"))
(assert (= d1 "Cookie:"))
(assert (= d (str.++ d1 a2)))
(assert (= b (str.++ c d)))
(assert (= var_S (str.++ a b)))

(check-sat)
