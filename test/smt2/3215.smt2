(set-logic UFNRA)
(set-option :model_validate true)
(set-option :model true)
(set-option :nlsat.inline_vars true)
(declare-const v0 Bool)
(declare-const v1 Bool)
(declare-const v2 Bool)
(declare-const v3 Bool)
(declare-const v4 Bool)
(declare-const v5 Bool)
(declare-const v6 Bool)
(declare-const v7 Bool)
(declare-const v8 Bool)
(declare-const v9 Bool)
(declare-const v10 Bool)
(declare-const v11 Bool)
(declare-const v12 Bool)
(declare-const v13 Bool)
(declare-const v14 Bool)
(declare-const v15 Bool)
(declare-const v16 Bool)
(declare-const v17 Bool)
(declare-const r0 Real)
(declare-sort S0 0)
(declare-const v18 Bool)
(declare-const r2 Real)
(declare-const v19 Bool)
(declare-sort S1 0)
(declare-const v20 Bool)
(declare-const v21 Bool)
(assert (exists ((q0 S0) (q1 S1) (q2 S0) (q3 Bool)) v19))
(assert (xor (and v4 v14 v20 (and v11 v10 v11 v7) v7 v15 v0 (= r0 (* 7 (- 7) r2 r0) (- 7) 7 (* 7 (- 7) r2 r0)) v13) v19 (= r0 (* 7 (- 7) r2 r0) (- 7) 7 (* 7 (- 7) r2 r0)) v11))
(declare-const v22 Bool)
(assert v12)
(assert v5)
(assert v7)
(declare-const v23 Bool)
;(assert (exists ((q4 Bool) (q5 S0) (q6 Bool)) (not (distinct q5 q5 q5 q5))))
(assert (=> (= (and v11 v10 v11 v7) v8 v8 (<= 7 (* 7 7 (* 7 (- 7) r2 r0) r0) r0 (* 7 (- 7) r2 r0) r2)) v6))
(declare-const S0-0 S0)
(declare-const v24 Bool)
(declare-const r3 Real)
(assert (and v17 v3 v24 v3 v3 v12))
(check-sat)