
; Copyright (c) 2015 Microsoft Corporation

(set-option :produce-models true)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(define-fun pOqOr () Bool (or p q r))
(define-fun np () Bool (not p))
(define-fun nq () Bool (not q))
(define-fun nr () Bool (not r))
(assert pOqOr)
(check-sat np)
(assert np)
(check-sat nq nr)