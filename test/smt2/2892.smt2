(define-fun f20 ((v291 String)) Bool
  (str.<= v291 (str.++ v291 "f")))

;(assert (f20 "\xf30\x1a\xdb~\xaa\xb9""JHG\x8c\x97G"))
(assert (f20 "7"))
(check-sat)