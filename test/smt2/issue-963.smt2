
(declare-fun c2 () Int)

(assert (<= 0 c2))
(assert (<= c2 8))
(assert (not (<= 0 (str.indexof "a123cdef" (str.substr "a123cdef" 0 c2) 0))))
(check-sat)
