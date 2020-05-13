; Copyright (c) 2018 Microsoft Corporation
; GitHub Issue

(declare-fun AB_serial_1_version_0 () String)
(declare-fun AB_serial_1_version_1 () String)

(assert (= (str.len AB_serial_1_version_0) 16))
(assert (= (str.len AB_serial_1_version_1) (str.len AB_serial_1_version_0)))
(assert (= (str.at AB_serial_1_version_1 15) (seq.unit #x00)))

(assert (= (str.indexof (str.substr AB_serial_1_version_1 0 (- 16 0)) (seq.unit #x00) 0) (- 0 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; if I use this instead, then both native z3                  ;
; and z3str3 return immediately with a (correct) unsat answer ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;(assert (= (str.indexof AB_serial_1_version_1 (seq.unit #x00) 0) (- 0 1)))

(check-sat)
(reset)

(set-option :smt.string_solver z3str3)

(declare-fun AB_serial_1_version_0 () String)
(declare-fun AB_serial_1_version_1 () String)

(assert (= (str.len AB_serial_1_version_0) 16))
(assert (= (str.len AB_serial_1_version_1) (str.len AB_serial_1_version_0)))
(assert (= (str.at AB_serial_1_version_1 15) (seq.unit #x00)))

(assert (= (str.indexof (str.substr AB_serial_1_version_1 0 (- 16 0)) (seq.unit #x00) 0) (- 0 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; if I use this instead, then both native z3                  ;
; and z3str3 return immediately with a (correct) unsat answer ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;(assert (= (str.indexof AB_serial_1_version_1 (seq.unit #x00) 0) (- 0 1)))

;; Disabled until z3str3 handles it.
(exit)
(check-sat)
(reset)
