(declare-fun a () String) 
(declare-fun b () String) 
(declare-fun c () String)
(declare-fun d () String)
(declare-fun e () String)
(assert
  (not
    (=
      (str.replace
        (str.++ "A" (str.substr a 0 (str.len c)))
        "A"
        (str.substr b 0 (str.len d))
      )
      (str.replace (str.substr a 0 (str.len c)) "" d)
    )
  )
)
(assert (= b (str.++ d e)))
(check-sat)   
;(get-model)
