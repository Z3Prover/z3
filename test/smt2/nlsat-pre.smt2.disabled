
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config true)
(declare-fun a () Real)
(assert (let ((a!1 (ite (>= (- (^ a 2.0)) 0.0) (- (^ a 2.0)) (- (- (^ a 2.0)))))) (not (= (^ a!1 (/ 1.0 2.0)) (^ (^ a 2.0) (/ 1.0 2.0))))))
(check-sat)
