; Copyright (c) 2018 Levent Erkok, Microsoft Corporation
; GitHub issue

(set-option :produce-models true)
(declare-fun x () Int)
(assert (>= 1 x))
(assert (<= 0 x))
(minimize x)
(maximize (+ x x))
(set-option :opt.priority pareto)
(check-sat)
(get-model)