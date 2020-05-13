
; Copyright (c) 2015 Microsoft Corporation
(set-option :smt.mbqi true)
(set-option :smt.ematching false)
(set-option :produce-models true)
; (set-logic UFLIA)
; define a new type Q:
(declare-sort Q 0)
; constants of type Q:
(declare-fun q_accept_S13 () Q)
(declare-fun q_T0_init () Q)
(declare-fun q_accept_S7 () Q)
(declare-fun q_accept_S6 () Q)
(declare-fun q_accept_S5 () Q)
(declare-fun q_accept_S4 () Q)
(declare-fun q_T0_S3 () Q)
(declare-fun q_accept_S12 () Q)
(declare-fun q_accept_S10 () Q)
(declare-fun q_accept_S9 () Q)
(declare-fun q_accept_all () Q)
; cardinality constraints:
(assert (forall ((q Q)) (or (= q q_accept_S13) (= q q_T0_init) (= q q_accept_S7) (= q q_accept_S6) (= q q_accept_S5) (= q q_accept_S4) (= q q_T0_S3) (= q q_accept_S12) (= q q_accept_S10) (= q q_accept_S9) (= q q_accept_all))))

; define a new type T:
(declare-sort T 0)
; constants of type T:
(declare-fun t_0 () T)
(declare-fun t_1 () T)
(declare-fun t_2 () T)
(declare-fun t_3 () T)
(declare-fun t_4 () T)
(declare-fun t_5 () T)
(declare-fun t_6 () T)
(declare-fun t_7 () T)
; cardinality constraints:
(assert (forall ((t T)) (or (= t t_0) (= t t_1) (= t t_2) (= t t_3) (= t t_4) (= t t_5) (= t t_6) (= t t_7))))

; define a new type Upsilon for the input letters:
(declare-sort Upsilon 0)
; constants of type Upsilon:
(declare-fun i_not_stop () Upsilon)
(declare-fun i_stop () Upsilon)

; Declarations for transition relation, output function and annotation
(declare-fun tau (T Upsilon) T)
(declare-fun fo_stop (T) Bool)
(declare-fun fo_c0 (T) Bool)
(declare-fun fo_c1 (T) Bool)
(declare-fun lambda_B (Q T) Bool)
(declare-fun lambda_sharp (Q T) Int)


; q=q_T0_init (q',v)=(q_accept_S7,i_not_stop), t=t_0
(assert (=> (and (lambda_B q_T0_init t_0) (fo_c1 t_0)) (and (lambda_B q_accept_S7 (tau t_0 i_not_stop)) (> (lambda_sharp q_accept_S7 (tau t_0 i_not_stop)) (lambda_sharp q_T0_init t_0)))))
; q=q_T0_init (q',v)=(q_accept_S7,i_not_stop), t=t_1
(assert (=> (and (lambda_B q_T0_init t_1) (fo_c1 t_1)) (and (lambda_B q_accept_S7 (tau t_1 i_not_stop)) (> (lambda_sharp q_accept_S7 (tau t_1 i_not_stop)) (lambda_sharp q_T0_init t_1)))))
; q=q_T0_init (q',v)=(q_accept_S7,i_not_stop), t=t_2
(assert (=> (and (lambda_B q_T0_init t_2) (fo_c1 t_2)) (and (lambda_B q_accept_S7 (tau t_2 i_not_stop)) (> (lambda_sharp q_accept_S7 (tau t_2 i_not_stop)) (lambda_sharp q_T0_init t_2)))))
; q=q_T0_init (q',v)=(q_accept_S7,i_not_stop), t=t_3
(assert (=> (and (lambda_B q_T0_init t_3) (fo_c1 t_3)) (and (lambda_B q_accept_S7 (tau t_3 i_not_stop)) (> (lambda_sharp q_accept_S7 (tau t_3 i_not_stop)) (lambda_sharp q_T0_init t_3)))))
; q=q_T0_init (q',v)=(q_accept_S7,i_not_stop), t=t_4
(assert (=> (and (lambda_B q_T0_init t_4) (fo_c1 t_4)) (and (lambda_B q_accept_S7 (tau t_4 i_not_stop)) (> (lambda_sharp q_accept_S7 (tau t_4 i_not_stop)) (lambda_sharp q_T0_init t_4)))))
; q=q_T0_init (q',v)=(q_accept_S7,i_not_stop), t=t_5
(assert (=> (and (lambda_B q_T0_init t_5) (fo_c1 t_5)) (and (lambda_B q_accept_S7 (tau t_5 i_not_stop)) (> (lambda_sharp q_accept_S7 (tau t_5 i_not_stop)) (lambda_sharp q_T0_init t_5)))))
; q=q_T0_init (q',v)=(q_accept_S7,i_not_stop), t=t_6
(assert (=> (and (lambda_B q_T0_init t_6) (fo_c1 t_6)) (and (lambda_B q_accept_S7 (tau t_6 i_not_stop)) (> (lambda_sharp q_accept_S7 (tau t_6 i_not_stop)) (lambda_sharp q_T0_init t_6)))))
; q=q_T0_init (q',v)=(q_accept_S7,i_not_stop), t=t_7
(assert (=> (and (lambda_B q_T0_init t_7) (fo_c1 t_7)) (and (lambda_B q_accept_S7 (tau t_7 i_not_stop)) (> (lambda_sharp q_accept_S7 (tau t_7 i_not_stop)) (lambda_sharp q_T0_init t_7)))))


;-------------- if comment any of these two calls the query becomes UNSAT
(push)
(check-sat)

; q=q_accept_S13 (q',v)=(q_accept_all,i_not_stop), t=t_0
(assert (=> (and (lambda_B q_accept_S13 t_0) (and (not (fo_stop t_0)) (fo_c0 t_0))) (and (lambda_B q_accept_all (tau t_0 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_0 i_not_stop)) (lambda_sharp q_accept_S13 t_0)))))
; q=q_accept_S13 (q',v)=(q_accept_all,i_not_stop), t=t_1
(assert (=> (and (lambda_B q_accept_S13 t_1) (and (not (fo_stop t_1)) (fo_c0 t_1))) (and (lambda_B q_accept_all (tau t_1 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_1 i_not_stop)) (lambda_sharp q_accept_S13 t_1)))))
; q=q_accept_S13 (q',v)=(q_accept_all,i_not_stop), t=t_2
(assert (=> (and (lambda_B q_accept_S13 t_2) (and (not (fo_stop t_2)) (fo_c0 t_2))) (and (lambda_B q_accept_all (tau t_2 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_2 i_not_stop)) (lambda_sharp q_accept_S13 t_2)))))
; q=q_accept_S13 (q',v)=(q_accept_all,i_not_stop), t=t_3
(assert (=> (and (lambda_B q_accept_S13 t_3) (and (not (fo_stop t_3)) (fo_c0 t_3))) (and (lambda_B q_accept_all (tau t_3 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_3 i_not_stop)) (lambda_sharp q_accept_S13 t_3)))))
; q=q_accept_S13 (q',v)=(q_accept_all,i_not_stop), t=t_4
(assert (=> (and (lambda_B q_accept_S13 t_4) (and (not (fo_stop t_4)) (fo_c0 t_4))) (and (lambda_B q_accept_all (tau t_4 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_4 i_not_stop)) (lambda_sharp q_accept_S13 t_4)))))
; q=q_accept_S13 (q',v)=(q_accept_all,i_not_stop), t=t_5
(assert (=> (and (lambda_B q_accept_S13 t_5) (and (not (fo_stop t_5)) (fo_c0 t_5))) (and (lambda_B q_accept_all (tau t_5 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_5 i_not_stop)) (lambda_sharp q_accept_S13 t_5)))))
; q=q_accept_S13 (q',v)=(q_accept_all,i_not_stop), t=t_6
(assert (=> (and (lambda_B q_accept_S13 t_6) (and (not (fo_stop t_6)) (fo_c0 t_6))) (and (lambda_B q_accept_all (tau t_6 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_6 i_not_stop)) (lambda_sharp q_accept_S13 t_6)))))
; q=q_accept_S13 (q',v)=(q_accept_all,i_not_stop), t=t_7
(assert (=> (and (lambda_B q_accept_S13 t_7) (and (not (fo_stop t_7)) (fo_c0 t_7))) (and (lambda_B q_accept_all (tau t_7 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_7 i_not_stop)) (lambda_sharp q_accept_S13 t_7)))))

; q=q_accept_S13 (q',v)=(q_accept_all,i_stop), t=t_0
(assert (=> (and (lambda_B q_accept_S13 t_0) (and (not (fo_stop t_0)) (fo_c0 t_0))) (and (lambda_B q_accept_all (tau t_0 i_stop)) (> (lambda_sharp q_accept_all (tau t_0 i_stop)) (lambda_sharp q_accept_S13 t_0)))))
; q=q_accept_S13 (q',v)=(q_accept_all,i_stop), t=t_1
(assert (=> (and (lambda_B q_accept_S13 t_1) (and (not (fo_stop t_1)) (fo_c0 t_1))) (and (lambda_B q_accept_all (tau t_1 i_stop)) (> (lambda_sharp q_accept_all (tau t_1 i_stop)) (lambda_sharp q_accept_S13 t_1)))))
; q=q_accept_S13 (q',v)=(q_accept_all,i_stop), t=t_2
(assert (=> (and (lambda_B q_accept_S13 t_2) (and (not (fo_stop t_2)) (fo_c0 t_2))) (and (lambda_B q_accept_all (tau t_2 i_stop)) (> (lambda_sharp q_accept_all (tau t_2 i_stop)) (lambda_sharp q_accept_S13 t_2)))))
; q=q_accept_S13 (q',v)=(q_accept_all,i_stop), t=t_3
(assert (=> (and (lambda_B q_accept_S13 t_3) (and (not (fo_stop t_3)) (fo_c0 t_3))) (and (lambda_B q_accept_all (tau t_3 i_stop)) (> (lambda_sharp q_accept_all (tau t_3 i_stop)) (lambda_sharp q_accept_S13 t_3)))))
; q=q_accept_S13 (q',v)=(q_accept_all,i_stop), t=t_4
(assert (=> (and (lambda_B q_accept_S13 t_4) (and (not (fo_stop t_4)) (fo_c0 t_4))) (and (lambda_B q_accept_all (tau t_4 i_stop)) (> (lambda_sharp q_accept_all (tau t_4 i_stop)) (lambda_sharp q_accept_S13 t_4)))))
; q=q_accept_S13 (q',v)=(q_accept_all,i_stop), t=t_5
(assert (=> (and (lambda_B q_accept_S13 t_5) (and (not (fo_stop t_5)) (fo_c0 t_5))) (and (lambda_B q_accept_all (tau t_5 i_stop)) (> (lambda_sharp q_accept_all (tau t_5 i_stop)) (lambda_sharp q_accept_S13 t_5)))))
; q=q_accept_S13 (q',v)=(q_accept_all,i_stop), t=t_6
(assert (=> (and (lambda_B q_accept_S13 t_6) (and (not (fo_stop t_6)) (fo_c0 t_6))) (and (lambda_B q_accept_all (tau t_6 i_stop)) (> (lambda_sharp q_accept_all (tau t_6 i_stop)) (lambda_sharp q_accept_S13 t_6)))))
; q=q_accept_S13 (q',v)=(q_accept_all,i_stop), t=t_7
(assert (=> (and (lambda_B q_accept_S13 t_7) (and (not (fo_stop t_7)) (fo_c0 t_7))) (and (lambda_B q_accept_all (tau t_7 i_stop)) (> (lambda_sharp q_accept_all (tau t_7 i_stop)) (lambda_sharp q_accept_S13 t_7)))))

; q=q_T0_init (q',v)=(q_accept_all,i_not_stop), t=t_0
(assert (=> (and (lambda_B q_T0_init t_0) (fo_c0 t_0)) (and (lambda_B q_accept_all (tau t_0 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_0 i_not_stop)) (lambda_sharp q_T0_init t_0)))))
; q=q_T0_init (q',v)=(q_accept_all,i_not_stop), t=t_1
(assert (=> (and (lambda_B q_T0_init t_1) (fo_c0 t_1)) (and (lambda_B q_accept_all (tau t_1 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_1 i_not_stop)) (lambda_sharp q_T0_init t_1)))))
; q=q_T0_init (q',v)=(q_accept_all,i_not_stop), t=t_2
(assert (=> (and (lambda_B q_T0_init t_2) (fo_c0 t_2)) (and (lambda_B q_accept_all (tau t_2 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_2 i_not_stop)) (lambda_sharp q_T0_init t_2)))))
; q=q_T0_init (q',v)=(q_accept_all,i_not_stop), t=t_3
(assert (=> (and (lambda_B q_T0_init t_3) (fo_c0 t_3)) (and (lambda_B q_accept_all (tau t_3 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_3 i_not_stop)) (lambda_sharp q_T0_init t_3)))))
; q=q_T0_init (q',v)=(q_accept_all,i_not_stop), t=t_4
(assert (=> (and (lambda_B q_T0_init t_4) (fo_c0 t_4)) (and (lambda_B q_accept_all (tau t_4 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_4 i_not_stop)) (lambda_sharp q_T0_init t_4)))))
; q=q_T0_init (q',v)=(q_accept_all,i_not_stop), t=t_5
(assert (=> (and (lambda_B q_T0_init t_5) (fo_c0 t_5)) (and (lambda_B q_accept_all (tau t_5 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_5 i_not_stop)) (lambda_sharp q_T0_init t_5)))))
; q=q_T0_init (q',v)=(q_accept_all,i_not_stop), t=t_6
(assert (=> (and (lambda_B q_T0_init t_6) (fo_c0 t_6)) (and (lambda_B q_accept_all (tau t_6 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_6 i_not_stop)) (lambda_sharp q_T0_init t_6)))))
; q=q_T0_init (q',v)=(q_accept_all,i_not_stop), t=t_7
(assert (=> (and (lambda_B q_T0_init t_7) (fo_c0 t_7)) (and (lambda_B q_accept_all (tau t_7 i_not_stop)) (> (lambda_sharp q_accept_all (tau t_7 i_not_stop)) (lambda_sharp q_T0_init t_7)))))


(check-sat)


(exit)