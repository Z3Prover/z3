
; Copyright (c) 2015 Microsoft Corporation
(set-option :print-success false )
(declare-fun x () Real )
(declare-fun y () Real )
(assert (< (to_real 0 ) x ) )
(assert (<= x y))
(assert
  (not
    (<= (/ (to_real 1 ) y ) (/ (to_real 1 ) x ) )
  )
)
(check-sat)

(reset)

(set-option :print-success false )
(set-option :auto-config true)
(declare-fun x () Real )
(declare-fun y () Real )
(assert (< (to_real 0 ) x ) )
(assert (<= x y))
(assert
  (not
    (<= (/ (to_real 1 ) y ) (/ (to_real 1 ) x ) )
  )
)
(check-sat)
