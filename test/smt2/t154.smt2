(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :auto-config false)
(set-option :model.v2 true)
(set-option :smt.phase-selection 0)
(set-option :smt.restart-strategy 0)
(set-option :smt.restart-factor 1.5)
(set-option :smt.arith.random-initial-value true)
(set-option :smt.case-split 3)
(set-option :smt.delay-units true)
(set-option :smt.delay-units-threshold 16)
(set-option :nnf.sk-hack true)
(set-option :smt.mbqi false)
(set-option :smt.qi.eager-threshold 100)
(set-option :smt.qi.cost "(+ weight generation)")
(set-option :type_check true)
(set-option :smt.bv.reflect true)
; done setting options

; Boogie universal background predicate
; Copyright (c) 2004-2010, Microsoft Corp.
(set-info :category "industrial")
(declare-sort |T@U| 0)
(declare-sort |T@T| 0)
(declare-fun int_div (Int Int) Int)
(declare-fun int_mod (Int Int) Int)
(declare-fun UOrdering2 (|T@U| |T@U|) Bool)
(declare-fun UOrdering3 (|T@T| |T@U| |T@U|) Bool)
(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))

(declare-fun %lbl%+346 () Bool)
(declare-fun x@0 () (Array Int Bool))
(declare-fun a@0 () (Array Int Int))
(declare-fun %lbl%@547 () Bool)
(declare-fun i () Int)
(declare-fun b@0 () (Array Int Int))
(declare-fun %lbl%@566 () Bool)
(declare-fun c@0 () (Array Int Int))
(declare-fun %lbl%@585 () Bool)
(declare-fun c@1 () (Array Int Int))
(declare-fun %lbl%@605 () Bool)
(declare-fun y@0 () (Array Int Bool))
(declare-fun %lbl%@619 () Bool)
(declare-fun %lbl%@623 () Bool)
(declare-fun y@1 () (Array Int Bool))
(declare-fun %lbl%@643 () Bool)
(declare-fun %lbl%@649 () Bool)
(declare-fun y@2 () (Array Int Bool))
(declare-fun %lbl%@667 () Bool)
(declare-fun %lbl%+505 () Bool)
(push 1)
(set-info :boogie-vc-id foo)
(assert (not
(let ((anon0_correct (=> (! (and %lbl%+346 true) :lblpos +346) (=> (and
(= x@0 ((as const (Array Int Bool)) true))
(= a@0 ((as const (Array Int Int)) 0))) (and
(! (or %lbl%@547 (= (select a@0 i) 0)) :lblneg @547)
(=> (= (select a@0 i) 0) (=> (= b@0 ((as const (Array Int Int)) 1)) (and
(! (or %lbl%@566 (= (select b@0 i) 1)) :lblneg @566)
(=> (= (select b@0 i) 1) (=> (= c@0 ((_ map (+ (Int Int) Int)) a@0 b@0)) (and
(! (or %lbl%@585 (= (select c@0 i) 1)) :lblneg @585)
(=> (= (select c@0 i) 1) (=> (= c@1 ((_ map (ite (Bool Int Int) Int)) x@0 a@0 b@0)) (and
(! (or %lbl%@605 (= c@1 a@0)) :lblneg @605)
(=> (= c@1 a@0) (=> (= y@0 ((_ map (<= (Int Int) Int)) c@1 a@0)) (and
(! (or %lbl%@619 (= x@0 y@0)) :lblneg @619)
(=> (= x@0 y@0) (and
(! (or %lbl%@623 (= ((_ map (= (Bool Bool) Bool)) x@0 y@0) ((as const (Array Int Bool)) true))) :lblneg @623)
(=> (= ((_ map (= (Bool Bool) Bool)) x@0 y@0) ((as const (Array Int Bool)) true)) (=> (= y@1 ((_ map (< (Int Int) Int)) c@1 a@0)) (and
(! (or %lbl%@643 (= ((_ map not) x@0) y@1)) :lblneg @643)
(=> (= ((_ map not) x@0) y@1) (and
(! (or %lbl%@649 false) :lblneg @649)
(=> false (=> (= y@2 ((_ map (= (Int Int) Bool)) ((as const (Array Int Int)) 0) ((as const (Array Int Int)) 1))) (and
(! (or %lbl%@667 (= ((_ map not) x@0) y@2)) :lblneg @667)
(=> (= ((_ map not) x@0) y@2) true))))))))))))))))))))))))))))
(let ((PreconditionGeneratedEntry_correct (=> (! (and %lbl%+505 true) :lblpos +505) anon0_correct)))
PreconditionGeneratedEntry_correct))
))
(check-sat)
(pop 1)
