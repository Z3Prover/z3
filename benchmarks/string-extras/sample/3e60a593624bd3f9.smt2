; origin: https://github.com/plfm-iis/trauc_benchmarks : ttt_047.smt2
(declare-fun g () String)
(declare-fun f () String)
(declare-fun a () String)
(declare-fun d () String)
(assert (= (str.++ "c" (str.++ d g)) (str.++ "e" (str.++ "g" "h"))))
(assert (= (str.++ d (str.++ "a" "a")) (str.++ "f" (str.++ a "e"))))
(assert (= (str.++ f (str.++ "d" "h")) (str.++ "f" (str.++ "e" "g"))))
(check-sat)
