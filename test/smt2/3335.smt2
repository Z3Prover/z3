(set-option :opt.priority box)
(set-option :opt.optsmt_engine farkas)
(set-option :model_validate true)
(set-option :model true)
(set-option :rewriter.flat false)
(declare-const v0 Bool)
(declare-const v1 Bool)
(declare-const v2 Bool)
(declare-const v3 Bool)
(declare-const i0 Int)
(declare-const i4 Int)
(declare-const i8 Int)
(declare-const i9 Int)
(declare-const v4 Bool)
(declare-const v5 Bool)
(declare-const v6 Bool)
(declare-const v7 Bool)
(declare-const v8 Bool)
(declare-const i10 Int)
(declare-const v9 Bool)
(declare-const i11 Int)
(declare-const v10 Bool)
(declare-const v11 Bool)
(declare-const v12 Bool)
(declare-const v13 Bool)
(declare-const v14 Bool)
(declare-const v15 Bool)
(assert (or v3 (> (div i8 i8) 55) v3))
(assert (or (> (* 60 (abs 95) 60) i8) (> (div i8 i8) 55) (> (* 60 (abs 95) 60) i8)))
(assert (or (> (* 60 (abs 95) 60) i8) (> (* 60 (abs 95) 60) i8) (> (* 60 (abs 95) 60) i8)))
(assert (or (> (* 60 (abs 95) 60) i8) (> (div i8 i8) 55) v3))
(assert (or v3 (> (div i8 i8) 55) (> (* 60 (abs 95) 60) i8)))
(assert (or (> (div i8 i8) 55) (> (* 60 (abs 95) 60) i8) (> (div i8 i8) 55)))
(assert (or (> (div i8 i8) 55) (> (* 60 (abs 95) 60) i8) (> (div i8 i8) 55)))
(assert (or (> (div i8 i8) 55) (> (* 60 (abs 95) 60) i8) (> (div i8 i8) 55)))
(assert (or (> (div i8 i8) 55) (> (div i8 i8) 55) v3))
(assert (or v3 (> (div i8 i8) 55) (> (div i8 i8) 55)))
(assert (or (> (* 60 (abs 95) 60) i8) (> (* 60 (abs 95) 60) i8) (> (div i8 i8) 55)))
(assert (or (> (div i8 i8) 55) (> (div i8 i8) 55) (> (div i8 i8) 55)))
(assert (or (> (* 60 (abs 95) 60) i8) (> (* 60 (abs 95) 60) i8) (> (* 60 (abs 95) 60) i8)))
(assert (or v3 v3 (> (* 60 (abs 95) 60) i8)))
(assert (or v3 (> (* 60 (abs 95) 60) i8) v3))
(minimize i0)
(minimize i4)
(minimize i8)
(minimize i9)
(maximize i10)
(maximize i11)
(check-sat)
(exit)
