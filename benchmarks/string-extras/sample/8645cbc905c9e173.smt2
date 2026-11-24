; origin: https://github.com/plfm-iis/trauc_benchmarks : ttt_039.smt2
(declare-fun g () String)
(declare-fun c () String)
(declare-fun e () String)
(declare-fun a () String)
(assert (= (str.++ "e" (str.++ "g" "f")) (str.++ e (str.++ "c" "h"))))
(assert (= (str.++ g (str.++ g "e")) (str.++ "d" (str.++ "b" a))))
(assert (= (str.++ "h" (str.++ "f" a)) (str.++ c (str.++ "a" "h"))))
(check-sat)
