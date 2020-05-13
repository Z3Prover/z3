;; Copyright (c) 2016 Microsoft Corporation 

(set-info :source |Written by D. B. Staple for Stack Overflow question 37711933.|)
(set-info :status unknown)

(declare-fun x () Real)
(assert (< (sin x) -1.0))
(check-sat)
