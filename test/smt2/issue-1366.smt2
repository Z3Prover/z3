; Copyright Microsoft 2017
; Source https://github.com/Z3Prover/z3/issues/1366 

(set-option :model_validate true)
(declare-fun name () String)
(assert (distinct (str.at name (str.indexof " " (str.substr name (str.len name) 1) 2)) ""))  ; this alone also is unsat
(check-sat)
(reset)

(set-option :model_validate true)
(declare-fun name () String)
(assert (= (str.at name (str.indexof " " (str.substr name (str.len name) 1) 2)) ""))  
(check-sat)
;(get-model)
;(eval (str.substr name (str.len name) 1))
;(eval (str.indexof " " (str.substr name (str.len name) 1) 2))
;(eval (str.at name (str.indexof " " (str.substr name (str.len name) 1) 2)))