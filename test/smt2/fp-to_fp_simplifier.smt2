
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)

(simplify (( _ to_fp 11 53 ) roundNearestTiesToEven 1.0 0)) 

(simplify (( _ to_fp 8 24 ) roundNearestTiesToEven 1.0 0)) 

(simplify ((_ to_fp 11 53) roundNearestTiesToEven
			(( _ to_fp 8 24 ) roundNearestTiesToEven 1.0 0)))
