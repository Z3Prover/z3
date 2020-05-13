
; Copyright (c) 2015 Microsoft Corporation

(set-option :model-validate false)

(set-option :auto-config true)
(declare-const a Real)
(declare-const b Real)

;; This is a corner case.
;; nlsat is currently creating a fresh variable for each division instead of using the uninterpreted functions.
;; The problem is that nlsat currently does not support uninterpreted functions. This will be fixed when
;; we integrate it in the main core.
;; So, this query must be marked back to unsat after we fix that.

;; current pre-processing multiplies with b
;; except for the case where b = 0.
;; Then pre-processing simplification takes are of this example

(assert (not (= (/ a b) (/ a 0.))))
(assert (<= b 0.))
(assert (>= b 0.))

(check-sat)

(reset)
(set-option :combined_solver.ignore_solver1 true)
(declare-const a Real)
(declare-const b Real)

(assert (not (= (/ a b) (/ a 0.))))
(assert (<= b 0.))
(assert (>= b 0.))

(check-sat)
