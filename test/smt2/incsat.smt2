
; Copyright (c) 2015 Microsoft Corporation
; test that incremental SAT solver works for QF_BV
(set-logic QF_BV)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)

(assert (or p q))
(check-sat)
(assert (or (not p) (not q)))
(check-sat)
(push)
(assert p)
(assert q)
(check-sat)
(pop)
(check-sat)

(declare-const x (_ BitVec 10))
(declare-const y (_ BitVec 10))
(declare-const z (_ BitVec 10))

(push)
(assert (not (= (bvor x y) (bvor y z))))
(check-sat)
(pop)