(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert
  (not
    (=
      (str.contains y (str.replace "A" (str.replace (str.++ x z) x "") z))
      (str.contains y "A")
    )
  )
)
(check-sat)     
