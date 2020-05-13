(set-logic NRA)
(set-option :model_validate true)
(set-option :model true)
(set-option :nlsat.inline_vars true)
(set-option :nlsat.shuffle_vars true)
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
(declare-const r0 Real)
(declare-const r1 Real)
(declare-const r2 Real)
(declare-const r3 Real)
(declare-const v12 Bool)
(declare-const v13 Bool)
(assert (forall ((q0 Bool) (q1 Real) (q2 Bool) (q3 Bool)) (not (> q1 q1 q1 q1 (/ r1 r2)))))
(declare-const r4 Real)
(declare-const v14 Bool)
(declare-const v15 Bool)
(declare-const v16 Bool)
(declare-const r5 Real)
(declare-const v17 Bool)
(declare-const v18 Bool)
(declare-const v19 Bool)
(assert (or (or v9 (and v1 v0 v2 v0 v2 v4 v9 v8 v1) v0 v3 v2 v2 v10) v16 v14))
(assert (or (not (>= r1 r3 (/ (/ r1 r2) r2))) v6 (<= 2800.0 (+ r0 (/ (/ r1 r2) r2) (/ (/ r1 r2) r2) r3) (* (/ (/ r1 r2) r1) 0.306148478 (/ (/ r3 r0) r1) r4 (/ 0.4801090 0.4801090)) (/ (/ r3 r0) r1))))
(assert (or (or v9 (and v1 v0 v2 v0 v2 v4 v9 v8 v1) v0 v3 v2 v2 v10) v14 v15))
(assert (or (and v1 v0 v2 v0 v2 v4 v9 v8 v1) (and v1 v0 v2 v0 v2 v4 v9 v8 v1) v3))
(assert (or v14 (>= r1 r3 (/ (/ r1 r2) r2)) v15))
(assert (or v3 v3 v15))
(assert (or v14 (not (>= r1 r3 (/ (/ r1 r2) r2))) (<= 2800.0 (+ r0 (/ (/ r1 r2) r2) (/ (/ r1 r2) r2) r3) (* (/ (/ r1 r2) r1) 0.306148478 (/ (/ r3 r0) r1) r4 (/ 0.4801090 0.4801090)) (/ (/ r3 r0) r1))))
(assert (or v15 v6 v14))
(assert (or v14 (or v9 (and v1 v0 v2 v0 v2 v4 v9 v8 v1) v0 v3 v2 v2 v10) v6))
(assert (or v16 (and v1 v0 v2 v0 v2 v4 v9 v8 v1) v15))
(assert (or (<= 2800.0 (+ r0 (/ (/ r1 r2) r2) (/ (/ r1 r2) r2) r3) (* (/ (/ r1 r2) r1) 0.306148478 (/ (/ r3 r0) r1) r4 (/ 0.4801090 0.4801090)) (/ (/ r3 r0) r1)) v14 (<= 2800.0 (+ r0 (/ (/ r1 r2) r2) (/ (/ r1 r2) r2) r3) (* (/ (/ r1 r2) r1) 0.306148478 (/ (/ r3 r0) r1) r4 (/ 0.4801090 0.4801090)) (/ (/ r3 r0) r1))))
(assert (or v6 (or v9 (and v1 v0 v2 v0 v2 v4 v9 v8 v1) v0 v3 v2 v2 v10) (or v9 (and v1 v0 v2 v0 v2 v4 v9 v8 v1) v0 v3 v2 v2 v10)))
(assert (or (not (>= r1 r3 (/ (/ r1 r2) r2))) v16 v15))
(assert (or v3 v6 v3))
(assert (or v15 (>= r1 r3 (/ (/ r1 r2) r2)) v16))
(assert (or (or v9 (and v1 v0 v2 v0 v2 v4 v9 v8 v1) v0 v3 v2 v2 v10) v6 v14))
(assert (or (not (>= r1 r3 (/ (/ r1 r2) r2))) v3 (and v1 v0 v2 v0 v2 v4 v9 v8 v1)))
(check-sat)