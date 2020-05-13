
; Copyright (c) 2015 Microsoft Corporation
(set-option :print-success false )
(declare-fun a () Real )
(declare-fun c () Real )
(declare-fun d () Real )
(assert (<= (to_real 0 ) a ) )
(assert (<= a (to_real 1 ) ) )
(assert (<= (to_real 0 ) d ) )
(assert (<= d c) )
(assert
  (not
    (<= (* a d) c)
  )
)
(check-sat)

