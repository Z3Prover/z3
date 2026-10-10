; Regression test for smt.qi.update_generation.
;
; Derived by ddSMT reduction from an F* query for Pulse.Lib.InsertionSort
; (FStarLang/FStar, pulse/lib/pulse/lib/Pulse.Lib.InsertionSort.fst): the
; preservation of the insertion-sort inner-loop invariant. The query is unsat;
; the set-options are those F* emits.
;
; Since #9628 (c3f5365a9), the internalizer lowers the generation of an
; already-internalized term when it is re-internalized at a lower generation.
; Here that greatly increases quantifier instantiation:
;
;                                       rlimit   quant-inst  decisions
;   z3 master, update_generation=false  0.57M      28k         5.5k
;   z3 master, update_generation=true   3.46M     177k        38.9k
;   z3 5.0.0 / 5.1.0 release            9.54M     494k
;   z3 4.15.8                           0.71M      36k
;
; Across smt.random_seed 0-8 (z3 master): false is unsat within 0.28M-0.68M;
; true needs 0.72M-12.0M and exceeds 2M on 8 of 9 seeds.
; The unreduced query (F*'s rlimit 7.5M): false 1.65M; true 45M.
;
; Expected with the rlimit below and the default seed:
;   z3 smt.qi.update_generation=false insertion_sort.smt2   ->  unsat
;   z3 smt.qi.update_generation=true  insertion_sort.smt2   ->  unknown
; See run.sh.
(set-option :global-decls false)
(set-option :smt.mbqi false)
(set-option :auto_config false)
(set-option :model true)
(set-option :smt.case_split 3)
(set-option :smt.relevancy 2)
(set-option :rewriter.enable_der false)
(set-option :rewriter.sort_disjunctions false)
(set-option :pi.decompose_patterns false)
(set-option :smt.arith.solver 6)
(set-option :smt.arith.nl.grobner_expand_terms false)
(declare-sort Term)
(declare-sort Universe)
(declare-fun U_zero () Universe)
(declare-fun U_succ (Universe) Universe)
(declare-fun ulevel ((Universe)) Int)
(declare-fun Univ (Int) Universe)
(declare-fun U_unif (Int) Universe)
(declare-fun U_unknown () Universe)
(declare-fun Term_constr_id (Term) Int)
(declare-sort Dummy_sort)
(declare-fun Dummy_value () Dummy_sort)
(declare-datatypes () ((Fuel (ZFuel) (SFuel (prec Fuel)))))
(declare-fun MaxIFuel () Fuel)
(declare-fun MaxFuel () Fuel)
(declare-fun PreType (Term) Term)
(declare-fun Valid (Term) Bool)
(declare-fun HasTypeFuel (Fuel Term Term) Bool)
(define-fun HasTypeZ ((x Term) (t Term)) Bool (HasTypeFuel ZFuel x t))
(define-fun HasType ((x Term) (t Term)) Bool (HasTypeFuel MaxIFuel x t))
(declare-fun IsTotFun (Term) Bool)
(declare-fun NoHoist (Term Bool) Bool)

;;no-hoist

(define-fun IsTyped ((x Term)) Bool (exists ((t Term)) (HasTypeZ x t)))
(declare-fun ApplyTF (Term Fuel) Term)
(declare-fun ApplyTT (Term Term) Term)
(declare-fun Prec (Term Term) Bool)
(declare-fun Closure (Term) Term)
(declare-fun ConsTerm (Term Term) Term)
(declare-fun ConsFuel (Fuel Term) Term)
(declare-fun Tm_uvar (Int) Term)
(define-fun Reify ((x Term)) Term x)
(declare-fun Prims.precedes (Universe Universe Term Term Term Term) Term)
(declare-fun Range_const (Int) Term)
(declare-fun _mul (Int Int) Int)
(declare-fun _div (Int Int) Int)
(declare-fun _rmul (Real Real) Real)
(declare-fun _rdiv (Real Real) Real)
(define-fun Unreachable () Bool false)

; Constructor

; Constructor distinct

; </end constructor FString_const>

; Constructor

(declare-fun Tm_type (Universe) Term)

; Constructor distinct

; Projection inverse

;;; Fact-ids: 

; Discriminator definition

; <start constructor Tm_arrow>

; Constructor

(declare-fun Tm_arrow (Int) Term)

; Constructor distinct

; Projector

(declare-fun Tm_arrow_id (Term) Int)
(assert (! (forall ((@u0 Int)) (! (= (Tm_arrow_id (Tm_arrow @u0)) @u0) :pattern ((Tm_arrow @u0)) :qid projection_inverse_Tm_arrow_id)) :named projection_inverse_Tm_arrow_id))
(declare-fun Tm_unit () Term)

; Constructor distinct

;;; Fact-ids: 

(assert (! (= 6 (Term_constr_id Tm_unit)) :named constructor_distinct_Tm_unit))

; Discriminator definition

(define-fun is-Tm_unit ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 6) (= __@x0 Tm_unit)))

; </end constructor Tm_unit>

; Constructor

(declare-fun BoxInt (Int) Term)
(declare-fun BoxInt_proj_0 (Term) Int)

; Projection inverse

;;; Fact-ids: 

(assert (! (forall ((@u0 Int)) (! (= (BoxInt_proj_0 (BoxInt @u0)) @u0) :pattern ((BoxInt @u0)) :qid projection_inverse_BoxInt_proj_0)) :named projection_inverse_BoxInt_proj_0))

; Discriminator definition

(define-fun is-BoxInt ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 7) (= __@x0 (BoxInt (BoxInt_proj_0 __@x0)))))

; </end constructor BoxInt>

; <start constructor BoxBool>

; Constructor

(declare-fun BoxBool (Bool) Term)

; Constructor distinct

;;; Fact-ids: 

(assert (! (forall ((@u0 Bool)) (! (= 8 (Term_constr_id (BoxBool @u0))) :pattern ((BoxBool @u0)) :qid constructor_distinct_BoxBool)) :named constructor_distinct_BoxBool))

; Projector

(declare-fun BoxBool_proj_0 (Term) Bool)

; Projection inverse

;;; Fact-ids: 

(assert (! (forall ((@u0 Bool)) (! (= (BoxBool_proj_0 (BoxBool @u0)) @u0) :pattern ((BoxBool @u0)) :qid projection_inverse_BoxBool_proj_0)) :named projection_inverse_BoxBool_proj_0))

; Discriminator definition

(define-fun is-BoxBool ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 8) (= __@x0 (BoxBool (BoxBool_proj_0 __@x0)))))

; Projector

(declare-fun LexCons_1 (Term) Term)

; Projection inverse

;;; Fact-ids: 

; Projector

(declare-fun LexCons_2 (Term) Term)

; Projection inverse

(declare-fun BoxProp (Bool) Term)
(declare-fun BoxProp_proj_0 (Term) Bool)

; Projection inverse

;;; Fact-ids: 

(declare-fun Prims.lex_t () Term)
(declare-fun LexTop () Term)
(declare-fun FStar.Ghost.erased (Universe Term) Term)
(declare-fun FStar.Ghost.hide (Universe Term Term) Term)
(declare-fun FStar.Ghost.reveal (Universe Term Term) Term)

; Constructor

(declare-fun FStar.Order.Eq () Term)

; data constructor proxy: FStar.Order.Eq

(declare-fun FStar.Order.Eq@tok () Term)

; Constructor

(declare-fun FStar.Order.Gt () Term)
(declare-fun FStar.Order.Gt@tok () Term)
(declare-fun FStar.Order.Lt () Term)

; data constructor proxy: FStar.Order.Lt

(declare-fun FStar.Order.Lt@tok () Term)
(declare-fun FStar.Order.eq (Term) Term)
(declare-fun FStar.Order.le (Term) Term)
(declare-fun FStar.Order.lt (Term) Term)

; Constructor

(declare-fun FStar.Order.order () Term)
(declare-fun FStar.Range.range (Dummy_sort) Term)
(declare-fun FStar.Seq.Base.empty (Universe Term) Term)
(declare-fun FStar.Seq.Base.index (Universe Term Term Term) Term)
(declare-fun FStar.Seq.Base.length (Universe Term Term) Term)
(declare-fun FStar.Seq.Base.seq (Universe Term) Term)
(declare-fun FStar.Seq.Base.slice (Universe Term Term Term Term) Term)
(declare-fun FStar.Seq.Base.upd (Universe Term Term Term Term) Term)
(declare-fun FStar.Seq.Properties.head (Universe Term Term) Term)
(declare-fun FStar.Seq.Properties.tail (Universe Term Term) Term)
(declare-fun FStar.SizeT.fits (Term) Term)
(declare-fun FStar.SizeT.lt (Term Term) Term)
(declare-fun FStar.SizeT.sub (Term Term Term) Term)
(declare-fun FStar.SizeT.t (Dummy_sort) Term)
(declare-fun FStar.SizeT.uint_to_t (Term Term) Term)
(declare-fun FStar.SizeT.v (Term) Term)

; Constructor

(declare-fun FStar.Stubs.Tactics.Common.NotAListLiteral () Term)

; Constructor base

(declare-fun FStar.Stubs.Tactics.Common.NotAListLiteral@base () Term)

; Constructor

(declare-fun FStar.Stubs.Tactics.Common.SKIP () Term)

; Constructor base

(declare-fun FStar.Stubs.Tactics.Common.SKIP@base () Term)

; Constructor base

; Constructor

(declare-fun FStar.Tactics.V2.Derived.Goal_not_trivial () Term)

; Constructor base

(declare-fun FStar.Tactics.V2.Derived.Goal_not_trivial@base () Term)
(declare-fun Prims.b2t (Term) Term)
(declare-fun Prims.bool () Term)
(declare-fun Prims.eqtype () Term)
(declare-fun Prims.hasEq (Universe Term) Term)
(declare-fun Prims.int () Term)
(declare-fun Prims.nat () Term)
(declare-fun Prims.not (Term) Term)
(declare-fun Prims.op_Equals (Term Term Term) Term)
(declare-fun Prims.op_Greater (Term Term) Term)
(declare-fun Prims.op_Greater_Equals (Term Term) Term)
(declare-fun Prims.op_Less (Term Term) Term)
(declare-fun Prims.op_Less_Equals (Term Term) Term)
(declare-fun Prims.op_Minus (Term Term) Term)
(declare-fun Prims.op_Plus (Term Term) Term)
(declare-fun Prims.op_Star (Term Term) Term)
(declare-fun Prims.pos () Term)
(declare-fun Prims.pow2.fuel_instrumented (Fuel Term) Term)
(declare-fun Prims.prop () Term)
(declare-fun Prims.squash (Term) Term)
(declare-fun Prims.unit () Term)
(declare-fun Pulse.Lib.InsertionSort.count (Universe Term Term Term Term) Term)
(declare-fun Pulse.Lib.InsertionSort.count.fuel_instrumented (Fuel Universe Term Term Term Term) Term)
(declare-fun Pulse.Lib.InsertionSort.inner_invariant (Universe Term Term Term Term Term Term Term Term) Term)
(declare-fun Pulse.Lib.InsertionSort.ordered (Universe Term Term Term Term) Term)
(declare-fun Pulse.Lib.InsertionSort.permutation (Universe Term Term Term Term) Term)
(declare-fun Pulse.Lib.InsertionSort.sorted (Universe Term Term Term) Term)

; Constructor

(declare-fun Pulse.Lib.TotalOrder.Mktotal_order (Universe Term Term Term) Term)

; Projector

(declare-fun Pulse.Lib.TotalOrder.Mktotal_order_@0 (Term) Universe)
(declare-fun Pulse.Lib.TotalOrder.Mktotal_order_@a (Term) Term)

; Projector

(declare-fun Pulse.Lib.TotalOrder.Mktotal_order_@compare (Term) Term)
(declare-fun Pulse.Lib.TotalOrder.Mktotal_order_@properties (Term) Term)
(declare-fun Pulse.Lib.TotalOrder.__proj__Mktotal_order__item__compare (Universe Term Term) Term)
(declare-fun Pulse.Lib.TotalOrder.flip_order (Term) Term)
(declare-fun Pulse.Lib.TotalOrder.op_Equals_Equals_Question (Universe Term Term Term Term) Term)
(declare-fun Pulse.Lib.TotalOrder.op_Greater_Equals_Question (Universe Term Term Term Term) Term)
(declare-fun Pulse.Lib.TotalOrder.op_Less_Equals_Question (Universe Term Term Term Term) Term)
(declare-fun Pulse.Lib.TotalOrder.op_Less_Question (Universe Term Term Term Term) Term)

; Constructor

(declare-fun Pulse.Lib.TotalOrder.total_order (Universe Term) Term)
(declare-fun Pulse.Lib.TotalOrder.total_order@tok (Universe) Term)
(declare-fun Tm_arrow_27cc418849843b85d0602c792e95b965 (Term Universe) Term)
(declare-fun Tm_refine_0817137556c8403efcddf9d82e1767c5 (Universe Term Term) Term)
(declare-fun Tm_refine_0ce91af3d6762ea7d913b870f9e33a01 (Universe Term) Term)
(declare-fun Tm_refine_160fe7faad9a466b3cae8455bac5be60 (Universe Term Term) Term)
(declare-fun Tm_refine_207024d2522be2ff59992eb07d6dc785 (Term) Term)
(declare-fun Tm_refine_2de20c066034c13bf76e9c0b94f4806c (Term) Term)
(declare-fun Tm_refine_542f9d4f129664613f2483a6c88bc7c2 () Term)
(declare-fun Tm_refine_5add1adb79e75abb939ada4dd8a7538f (Term Term) Term)
(declare-fun Tm_refine_6cba8b694d7fbf759331b42d86bb8cbd (Universe Term Term Term) Term)
(declare-fun Tm_refine_774ba3f728d91ead8ef40be66c9802e5 () Term)
(declare-fun Tm_refine_7df43cb9feb536df62477b7b30ce1682 () Term)
(declare-fun Tm_refine_89f93f0d2f57e09801995b3283389610 (Term Term) Term)
(declare-fun Tm_refine_9d6af3f3535473623f7aec2f0501897f () Term)
(declare-fun Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1 (Universe Term) Term)
(declare-fun Tm_refine_c8cc915fa69008ea6ec6c900835be1d5 (Universe Term Term Term) Term)
(declare-fun Tm_refine_cbe1f197f91af0696ac962995d5b2280 (Term Term) Term)
(declare-fun Tm_refine_cc0abff8026303d2626cb79040e5c59e (Universe Term Term) Term)
(declare-fun Tm_refine_cf7cf1886ab56e79bff605f06a0f72bc (Universe Term Term) Term)
(declare-fun Tm_refine_d7ac964e93ed768e3b6dc5dc2457c982 (Universe Term Term) Term)
(declare-fun Tm_refine_ee3137b5d9f07244c499a05a59dd12e7 (Universe Term Term Term) Term)
(define-fun is-FStar.Order.Eq ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 109) (= __@x0 FStar.Order.Eq)))
(define-fun is-FStar.Stubs.Tactics.Common.NotAListLiteral ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 102) (= __@x0 FStar.Stubs.Tactics.Common.NotAListLiteral)))

; Discriminator definition

(define-fun is-FStar.Stubs.Tactics.Common.SKIP ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 117) (= __@x0 FStar.Stubs.Tactics.Common.SKIP)))

; Discriminator definition

; Discriminator definition

(define-fun is-FStar.Tactics.V2.Derived.Goal_not_trivial ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 115) (= __@x0 FStar.Tactics.V2.Derived.Goal_not_trivial)))

; Discriminator definition

(define-fun is-Pulse.Lib.TotalOrder.Mktotal_order ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 113) (= __@x0 (Pulse.Lib.TotalOrder.Mktotal_order (Pulse.Lib.TotalOrder.Mktotal_order_@0 __@x0) (Pulse.Lib.TotalOrder.Mktotal_order_@a __@x0) (Pulse.Lib.TotalOrder.Mktotal_order_@compare __@x0) (Pulse.Lib.TotalOrder.Mktotal_order_@properties __@x0)))))

; Correspondence of recursive function to instrumented version

;;; Fact-ids: Name Pulse.Lib.InsertionSort.count; Namespace Pulse.Lib.InsertionSort

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term)) (! (= (Pulse.Lib.InsertionSort.count @u0 @x1 @x2 @x3 @x4) (Pulse.Lib.InsertionSort.count.fuel_instrumented MaxFuel @u0 @x1 @x2 @x3 @x4)) :pattern ((Pulse.Lib.InsertionSort.count @u0 @x1 @x2 @x3 @x4)) :qid @fuel_correspondence_Pulse.Lib.InsertionSort.count.fuel_instrumented)) :named @fuel_correspondence_Pulse.Lib.InsertionSort.count.fuel_instrumented))

; Fuel irrelevance

; bool typing

;;; Fact-ids: Name Prims.bool; Namespace Prims

; Constructor base

;;; Fact-ids: Name FStar.Stubs.Tactics.Common.NotAListLiteral; Namespace FStar.Stubs.Tactics.Common

(assert (! (implies (is-FStar.Stubs.Tactics.Common.NotAListLiteral FStar.Stubs.Tactics.Common.NotAListLiteral) (= FStar.Stubs.Tactics.Common.NotAListLiteral FStar.Stubs.Tactics.Common.NotAListLiteral@base)) :named constructor_base_FStar.Stubs.Tactics.Common.NotAListLiteral))

; Constructor base

;;; Fact-ids: Name FStar.Stubs.Tactics.Common.SKIP; Namespace FStar.Stubs.Tactics.Common

(assert (! (implies (is-FStar.Stubs.Tactics.Common.SKIP FStar.Stubs.Tactics.Common.SKIP) (= FStar.Stubs.Tactics.Common.SKIP FStar.Stubs.Tactics.Common.SKIP@base)) :named constructor_base_FStar.Stubs.Tactics.Common.SKIP))

; Constructor base

;;; Fact-ids: Name FStar.Stubs.Tactics.Common.Stop; Namespace FStar.Stubs.Tactics.Common

(assert (! (implies (is-FStar.Tactics.V2.Derived.Goal_not_trivial FStar.Tactics.V2.Derived.Goal_not_trivial) (= FStar.Tactics.V2.Derived.Goal_not_trivial FStar.Tactics.V2.Derived.Goal_not_trivial@base)) :named constructor_base_FStar.Tactics.V2.Derived.Goal_not_trivial))

; Constructor distinct

;;; Fact-ids: Name FStar.Ghost.erased; Namespace FStar.Ghost

; Constructor distinct

;;; Fact-ids: Name FStar.Order.order; Namespace FStar.Order; Name FStar.Order.Lt; Namespace FStar.Order; Name FStar.Order.Eq; Namespace FStar.Order; Name FStar.Order.Gt; Namespace FStar.Order

(assert (! (= 109 (Term_constr_id FStar.Order.Eq)) :named constructor_distinct_FStar.Order.Eq))

; Constructor distinct

(assert (! (= 107 (Term_constr_id FStar.Order.Lt)) :named constructor_distinct_FStar.Order.Lt))

;;; Fact-ids: Name Pulse.Lib.TotalOrder.total_order; Namespace Pulse.Lib.TotalOrder; Name Pulse.Lib.TotalOrder.Mktotal_order; Namespace Pulse.Lib.TotalOrder

(assert (! (forall ((@u0 Universe) (@x1 Term)) (! (= 103 (Term_constr_id (Pulse.Lib.TotalOrder.total_order @u0 @x1))) :pattern ((Pulse.Lib.TotalOrder.total_order @u0 @x1)) :qid constructor_distinct_Pulse.Lib.TotalOrder.total_order)) :named constructor_distinct_Pulse.Lib.TotalOrder.total_order))

; data constructor typing elim

;;; Fact-ids: Name Pulse.Lib.TotalOrder.total_order; Namespace Pulse.Lib.TotalOrder; Name Pulse.Lib.TotalOrder.Mktotal_order; Namespace Pulse.Lib.TotalOrder

(assert (! (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term)) (! (implies (HasTypeFuel (SFuel @u0) (Pulse.Lib.TotalOrder.Mktotal_order @u1 @x2 @x3 @x4) (Pulse.Lib.TotalOrder.total_order @u1 @x5)) (and (HasTypeFuel @u0 @x5 (Tm_type @u1)) (HasTypeFuel @u0 @x3 (Tm_arrow_27cc418849843b85d0602c792e95b965 @x5 @u1)) (HasTypeFuel @u0 @x4 (Tm_refine_d7ac964e93ed768e3b6dc5dc2457c982 @u1 @x5 @x3)))) :pattern ((HasTypeFuel (SFuel @u0) (Pulse.Lib.TotalOrder.Mktotal_order @u1 @x2 @x3 @x4) (Pulse.Lib.TotalOrder.total_order @u1 @x5))) :qid data_elim_Pulse.Lib.TotalOrder.Mktotal_order)) :named data_elim_Pulse.Lib.TotalOrder.Mktotal_order))

; data constructor typing intro

;;; Fact-ids: Name FStar.Order.order; Namespace FStar.Order; Name FStar.Order.Lt; Namespace FStar.Order; Name FStar.Order.Eq; Namespace FStar.Order; Name FStar.Order.Gt; Namespace FStar.Order

(assert (! (= FStar.Order.Eq@tok FStar.Order.Eq) :named equality_tok_FStar.Order.Eq@tok))

; equality for proxy

;;; Fact-ids: Name FStar.Order.order; Namespace FStar.Order; Name FStar.Order.Lt; Namespace FStar.Order; Name FStar.Order.Eq; Namespace FStar.Order; Name FStar.Order.Gt; Namespace FStar.Order

; equality for proxy

;;; Fact-ids: Name FStar.Order.order; Namespace FStar.Order; Name FStar.Order.Lt; Namespace FStar.Order; Name FStar.Order.Eq; Namespace FStar.Order; Name FStar.Order.Gt; Namespace FStar.Order

(assert (! (= FStar.Order.Lt@tok FStar.Order.Lt) :named equality_tok_FStar.Order.Lt@tok))
(assert (! (forall ((@x0 Term)) (! (= (FStar.Order.eq @x0) (Prims.op_Equals FStar.Order.order @x0 FStar.Order.Eq@tok)) :pattern ((FStar.Order.eq @x0)) :qid equation_FStar.Order.eq)) :named equation_FStar.Order.eq))

;;; Fact-ids: Name FStar.Order.le; Namespace FStar.Order

; Equation for FStar.Order.lt

;;; Fact-ids: Name FStar.Order.lt; Namespace FStar.Order

(assert (! (forall ((@x0 Term)) (! (= (FStar.Order.lt @x0) (Prims.op_Equals FStar.Order.order @x0 FStar.Order.Lt@tok)) :pattern ((FStar.Order.lt @x0)) :qid equation_FStar.Order.lt)) :named equation_FStar.Order.lt))

;;; Fact-ids: Name FStar.Seq.Properties.head; Namespace FStar.Seq.Properties

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term)) (! (= (FStar.Seq.Properties.head @u0 @x1 @x2) (FStar.Seq.Base.index @u0 @x1 @x2 (BoxInt 0))) :pattern ((FStar.Seq.Properties.head @u0 @x1 @x2)) :qid equation_FStar.Seq.Properties.head)) :named equation_FStar.Seq.Properties.head))

; Equation for FStar.Seq.Properties.tail

;;; Fact-ids: Name FStar.Seq.Properties.tail; Namespace FStar.Seq.Properties

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term)) (! (= (FStar.Seq.Properties.tail @u0 @x1 @x2) (FStar.Seq.Base.slice @u0 @x1 @x2 (BoxInt 1) (FStar.Seq.Base.length @u0 @x1 @x2))) :pattern ((FStar.Seq.Properties.tail @u0 @x1 @x2)) :qid equation_FStar.Seq.Properties.tail)) :named equation_FStar.Seq.Properties.tail))

; Equation for Prims.eqtype

;;; Fact-ids: Name Prims.eqtype; Namespace Prims

(assert (! (= Prims.eqtype Tm_refine_9d6af3f3535473623f7aec2f0501897f) :named equation_Prims.eqtype))

; Equation for Prims.nat

;;; Fact-ids: Name Prims.nat; Namespace Prims

(assert (! (= Prims.nat Tm_refine_542f9d4f129664613f2483a6c88bc7c2) :named equation_Prims.nat))

; Equation for Prims.pos

;;; Fact-ids: Name Prims.pos; Namespace Prims

;;; Fact-ids: Name Prims.squash; Namespace Prims

(assert (! (forall ((@x0 Term)) (! (= (Prims.squash @x0) (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0)) :pattern ((Prims.squash @x0)) :qid equation_Prims.squash)) :named equation_Prims.squash))

; Equation for Pulse.Lib.Core.rewrites_to_p

;;; Fact-ids: Name Pulse.Lib.Core.rewrites_to_p; Namespace Pulse.Lib.Core

; Equation for Pulse.Lib.InsertionSort.inner_invariant

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term)) (! (= (Valid (Pulse.Lib.InsertionSort.inner_invariant @u0 @x1 @x2 @x3 @x4 @x5 @x6 @x7 @x8)) (and (<= (BoxInt_proj_0 (BoxInt 0)) (BoxInt_proj_0 (FStar.SizeT.v @x6))) (< (BoxInt_proj_0 (FStar.SizeT.v @x6)) (BoxInt_proj_0 (FStar.SizeT.v @x7))) (< (BoxInt_proj_0 (FStar.SizeT.v @x7)) (BoxInt_proj_0 (FStar.Seq.Base.length @u0 @x1 @x4))) (Valid (Pulse.Lib.InsertionSort.sorted @u0 @x1 @x2 (FStar.Seq.Base.slice @u0 @x1 @x4 (BoxInt 0) (Prims.op_Plus (FStar.SizeT.v @x6) (BoxInt 1))))) (Valid (Pulse.Lib.InsertionSort.sorted @u0 @x1 @x2 (FStar.Seq.Base.slice @u0 @x1 @x4 (Prims.op_Plus (FStar.SizeT.v @x6) (BoxInt 1)) (Prims.op_Plus (FStar.SizeT.v @x7) (BoxInt 1))))) (Valid (Pulse.Lib.InsertionSort.ordered @u0 @x1 @x2 (FStar.Seq.Base.slice @u0 @x1 @x4 (BoxInt 0) (Prims.op_Plus (FStar.SizeT.v @x6) (BoxInt 1))) (FStar.Seq.Base.upd @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x4 (Prims.op_Plus (FStar.SizeT.v @x6) (BoxInt 1)) (Prims.op_Plus (FStar.SizeT.v @x7) (BoxInt 1))) (BoxInt 0) (FStar.Seq.Base.index @u0 @x1 @x4 (FStar.SizeT.v @x6))))) (let ((@lb9 @x8)) (ite (= @lb9 (BoxBool true)) (and (= @x6 (FStar.SizeT.uint_to_t (BoxInt 0) Tm_unit)) (= (FStar.Seq.Base.index @u0 @x1 @x4 (Prims.op_Plus (FStar.SizeT.v @x6) (BoxInt 1))) (FStar.Seq.Base.index @u0 @x1 @x4 (FStar.SizeT.v @x6))) (Valid (Pulse.Lib.InsertionSort.permutation @u0 @x1 @x2 @x3 (FStar.Seq.Base.upd @u0 @x1 @x4 (BoxInt 0) @x5)))) (let ((@lb10 (Prims.op_Equals Prims.int (Prims.op_Plus (FStar.SizeT.v @x6) (BoxInt 1)) (FStar.SizeT.v @x7)))) (ite (= @lb10 (BoxBool true)) (and (= (FStar.Seq.Base.index @u0 @x1 @x4 (Prims.op_Plus (FStar.SizeT.v @x6) (BoxInt 1))) @x5) (Valid (Pulse.Lib.InsertionSort.permutation @u0 @x1 @x2 @x3 @x4))) (and (= (FStar.Seq.Base.index @u0 @x1 @x4 (Prims.op_Plus (FStar.SizeT.v @x6) (BoxInt 1))) (FStar.Seq.Base.index @u0 @x1 @x4 (Prims.op_Plus (FStar.SizeT.v @x6) (BoxInt 2)))) (Valid (Pulse.Lib.InsertionSort.permutation @u0 @x1 @x2 @x3 (FStar.Seq.Base.upd @u0 @x1 @x4 (Prims.op_Plus (FStar.SizeT.v @x6) (BoxInt 1)) @x5)))))))) (forall ((@x9 Term)) (! (implies (and (HasType @x9 Prims.nat) (<= (BoxInt_proj_0 (BoxInt 0)) (BoxInt_proj_0 @x9)) (< (BoxInt_proj_0 @x9) (BoxInt_proj_0 (FStar.Seq.Base.length @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x4 (Prims.op_Plus (FStar.SizeT.v @x6) (BoxInt 1)) (Prims.op_Plus (FStar.SizeT.v @x7) (BoxInt 1))))))) (BoxBool_proj_0 (Pulse.Lib.TotalOrder.op_Greater_Equals_Question @u0 @x1 @x2 (FStar.Seq.Base.index @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x4 (Prims.op_Plus (FStar.SizeT.v @x6) (BoxInt 1)) (Prims.op_Plus (FStar.SizeT.v @x7) (BoxInt 1))) @x9) @x5))) :qid equation_Pulse.Lib.InsertionSort.inner_invariant.1)))) :pattern ((Pulse.Lib.InsertionSort.inner_invariant @u0 @x1 @x2 @x3 @x4 @x5 @x6 @x7 @x8)) :qid equation_Pulse.Lib.InsertionSort.inner_invariant)) :named equation_Pulse.Lib.InsertionSort.inner_invariant))
(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term)) (! (= (Valid (Pulse.Lib.InsertionSort.ordered @u0 @x1 @x2 @x3 @x4)) (forall ((@x5 Term) (@x6 Term)) (! (implies (and (HasType @x5 (Tm_refine_cc0abff8026303d2626cb79040e5c59e @u0 @x1 @x3)) (HasType @x6 (Tm_refine_cc0abff8026303d2626cb79040e5c59e @u0 @x1 @x4)) (<= (BoxInt_proj_0 (BoxInt 0)) (BoxInt_proj_0 @x5)) (< (BoxInt_proj_0 @x5) (BoxInt_proj_0 (FStar.Seq.Base.length @u0 @x1 @x3))) (<= (BoxInt_proj_0 (BoxInt 0)) (BoxInt_proj_0 @x6)) (< (BoxInt_proj_0 @x6) (BoxInt_proj_0 (FStar.Seq.Base.length @u0 @x1 @x4)))) (BoxBool_proj_0 (Pulse.Lib.TotalOrder.op_Less_Equals_Question @u0 @x1 @x2 (FStar.Seq.Base.index @u0 @x1 @x3 @x5) (FStar.Seq.Base.index @u0 @x1 @x4 @x6)))) :qid equation_Pulse.Lib.InsertionSort.ordered.1))) :pattern ((Pulse.Lib.InsertionSort.ordered @u0 @x1 @x2 @x3 @x4)) :qid equation_Pulse.Lib.InsertionSort.ordered)) :named equation_Pulse.Lib.InsertionSort.ordered))

; Equation for Pulse.Lib.InsertionSort.permutation

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term)) (! (= (Valid (Pulse.Lib.InsertionSort.permutation @u0 @x1 @x2 @x3 @x4)) (forall ((@x5 Term)) (! (implies (HasType @x5 @x1) (= (Pulse.Lib.InsertionSort.count @u0 @x1 @x2 @x5 @x3) (Pulse.Lib.InsertionSort.count @u0 @x1 @x2 @x5 @x4))) :qid equation_Pulse.Lib.InsertionSort.permutation.1))) :pattern ((Pulse.Lib.InsertionSort.permutation @u0 @x1 @x2 @x3 @x4)) :qid equation_Pulse.Lib.InsertionSort.permutation)) :named equation_Pulse.Lib.InsertionSort.permutation))
(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term)) (! (= (Valid (Pulse.Lib.InsertionSort.sorted @u0 @x1 @x2 @x3)) (forall ((@x4 Term) (@x5 Term)) (! (implies (and (HasType @x4 Prims.nat) (HasType @x5 Prims.nat) (<= (BoxInt_proj_0 @x4) (BoxInt_proj_0 @x5)) (< (BoxInt_proj_0 @x5) (BoxInt_proj_0 (FStar.Seq.Base.length @u0 @x1 @x3)))) (BoxBool_proj_0 (Pulse.Lib.TotalOrder.op_Less_Equals_Question @u0 @x1 @x2 (FStar.Seq.Base.index @u0 @x1 @x3 @x4) (FStar.Seq.Base.index @u0 @x1 @x3 @x5)))) :pattern ((FStar.Seq.Base.index @u0 @x1 @x3 @x4) (FStar.Seq.Base.index @u0 @x1 @x3 @x5)) :qid equation_Pulse.Lib.InsertionSort.sorted.1))) :pattern ((Pulse.Lib.InsertionSort.sorted @u0 @x1 @x2 @x3)) :qid equation_Pulse.Lib.InsertionSort.sorted)) :named equation_Pulse.Lib.InsertionSort.sorted))

;;; Fact-ids: Name Pulse.Lib.TotalOrder.flip_order; Namespace Pulse.Lib.TotalOrder

; Equation for Pulse.Lib.TotalOrder.op_Equals_Equals_Question

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term)) (! (= (Pulse.Lib.TotalOrder.op_Equals_Equals_Question @u0 @x1 @x2 @x3 @x4) (FStar.Order.eq (ApplyTT (ApplyTT (Pulse.Lib.TotalOrder.__proj__Mktotal_order__item__compare @u0 @x1 @x2) @x3) @x4))) :pattern ((Pulse.Lib.TotalOrder.op_Equals_Equals_Question @u0 @x1 @x2 @x3 @x4)) :qid equation_Pulse.Lib.TotalOrder.op_Equals_Equals_Question)) :named equation_Pulse.Lib.TotalOrder.op_Equals_Equals_Question))

; Equation for Pulse.Lib.TotalOrder.op_Greater_Equals_Question

;;; Fact-ids: Name Pulse.Lib.TotalOrder.op_Greater_Equals_Question; Namespace Pulse.Lib.TotalOrder

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term)) (! (= (Pulse.Lib.TotalOrder.op_Greater_Equals_Question @u0 @x1 @x2 @x3 @x4) (Prims.not (Pulse.Lib.TotalOrder.op_Less_Question @u0 @x1 @x2 @x3 @x4))) :pattern ((Pulse.Lib.TotalOrder.op_Greater_Equals_Question @u0 @x1 @x2 @x3 @x4)) :qid equation_Pulse.Lib.TotalOrder.op_Greater_Equals_Question)) :named equation_Pulse.Lib.TotalOrder.op_Greater_Equals_Question))

; Equation for Pulse.Lib.TotalOrder.op_Less_Equals_Question

;;; Fact-ids: Name Pulse.Lib.TotalOrder.op_Less_Equals_Question; Namespace Pulse.Lib.TotalOrder

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term)) (! (= (Pulse.Lib.TotalOrder.op_Less_Equals_Question @u0 @x1 @x2 @x3 @x4) (FStar.Order.le (ApplyTT (ApplyTT (Pulse.Lib.TotalOrder.__proj__Mktotal_order__item__compare @u0 @x1 @x2) @x3) @x4))) :pattern ((Pulse.Lib.TotalOrder.op_Less_Equals_Question @u0 @x1 @x2 @x3 @x4)) :qid equation_Pulse.Lib.TotalOrder.op_Less_Equals_Question)) :named equation_Pulse.Lib.TotalOrder.op_Less_Equals_Question))

; Equation for Pulse.Lib.TotalOrder.op_Less_Question

;;; Fact-ids: Name Pulse.Lib.TotalOrder.op_Less_Question; Namespace Pulse.Lib.TotalOrder

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term)) (! (= (Pulse.Lib.TotalOrder.op_Less_Question @u0 @x1 @x2 @x3 @x4) (FStar.Order.lt (ApplyTT (ApplyTT (Pulse.Lib.TotalOrder.__proj__Mktotal_order__item__compare @u0 @x1 @x2) @x3) @x4))) :pattern ((Pulse.Lib.TotalOrder.op_Less_Question @u0 @x1 @x2 @x3 @x4)) :qid equation_Pulse.Lib.TotalOrder.op_Less_Question)) :named equation_Pulse.Lib.TotalOrder.op_Less_Question))

; Equation for fuel-instrumented recursive function: Prims.pow2

;;; Fact-ids: Name Prims.pow2; Namespace Prims

;;; Fact-ids: Name Pulse.Lib.InsertionSort.count; Namespace Pulse.Lib.InsertionSort

(assert (! (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term)) (! (implies (and (HasType @x2 (Tm_type @u1)) (HasType @x3 (Pulse.Lib.TotalOrder.total_order @u1 @x2)) (HasType @x4 @x2) (HasType @x5 (FStar.Seq.Base.seq @u1 @x2))) (= (Pulse.Lib.InsertionSort.count.fuel_instrumented (SFuel @u0) @u1 @x2 @x3 @x4 @x5) (let ((@lb6 (Prims.op_Equals Prims.int (FStar.Seq.Base.length @u1 @x2 @x5) (BoxInt 0)))) (ite (= @lb6 (BoxBool true)) (BoxInt 0) (let ((@lb7 (Pulse.Lib.TotalOrder.op_Equals_Equals_Question @u1 @x2 @x3 (FStar.Seq.Properties.head @u1 @x2 @x5) @x4))) (ite (= @lb7 (BoxBool true)) (Prims.op_Plus (BoxInt 1) (Pulse.Lib.InsertionSort.count.fuel_instrumented @u0 @u1 @x2 @x3 @x4 (FStar.Seq.Properties.tail @u1 @x2 @x5))) (Pulse.Lib.InsertionSort.count.fuel_instrumented @u0 @u1 @x2 @x3 @x4 (FStar.Seq.Properties.tail @u1 @x2 @x5)))))))) :weight 0 :pattern ((Pulse.Lib.InsertionSort.count.fuel_instrumented (SFuel @u0) @u1 @x2 @x3 @x4 @x5)) :qid equation_with_fuel_Pulse.Lib.InsertionSort.count.fuel_instrumented)) :named equation_with_fuel_Pulse.Lib.InsertionSort.count.fuel_instrumented))

; fresh token

;;; Fact-ids: Name Pulse.Lib.TotalOrder.total_order; Namespace Pulse.Lib.TotalOrder; Name Pulse.Lib.TotalOrder.Mktotal_order; Namespace Pulse.Lib.TotalOrder

; inversion axiom

(assert (! (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term)) (! (implies (HasTypeFuel @u0 @x1 (Pulse.Lib.TotalOrder.total_order @u2 @x3)) (and (is-Pulse.Lib.TotalOrder.Mktotal_order @x1) (= @u2 (Pulse.Lib.TotalOrder.Mktotal_order_@0 @x1)) (= @x3 (Pulse.Lib.TotalOrder.Mktotal_order_@a @x1)))) :pattern ((HasTypeFuel @u0 @x1 (Pulse.Lib.TotalOrder.total_order @u2 @x3))) :qid fuel_guarded_inversion_Pulse.Lib.TotalOrder.total_order)) :named fuel_guarded_inversion_Pulse.Lib.TotalOrder.total_order))

; function token typing

; haseq for Tm_refine_c8cc915fa69008ea6ec6c900835be1d5

(assert (! (forall ((@u0 Fuel) (@x1 Term)) (! (implies (HasTypeFuel @u0 @x1 Prims.int) (is-BoxInt @x1)) :pattern ((HasTypeFuel @u0 @x1 Prims.int)) :qid int_inversion)) :named int_inversion))

; int typing

;;; Fact-ids: Name Prims.int; Namespace Prims

(assert (! (forall ((@u0 Int)) (! (HasType (BoxInt @u0) Prims.int) :pattern ((BoxInt @u0)) :qid int_typing)) :named int_typing))

; Lemma: FStar.Ghost.hide_reveal

; Lemma: FStar.Int.pow2_values

;;; Fact-ids: Name FStar.Int.pow2_values; Namespace FStar.Int

(assert (! (forall ((@x0 Term)) (! (implies (HasType @x0 Prims.nat) (let ((@lb1 @x0)) (ite (= @lb1 (BoxInt 0)) (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 1)) (ite (= @lb1 (BoxInt 1)) (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 2)) (ite (= @lb1 (BoxInt 8)) (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 256)) (ite (= @lb1 (BoxInt 16)) (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 65536)) (ite (= @lb1 (BoxInt 31)) (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 2147483648)) (ite (= @lb1 (BoxInt 32)) (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 4294967296)) (ite (= @lb1 (BoxInt 63)) (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 9223372036854775808)) (implies (= @lb1 (BoxInt 64)) (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 18446744073709551616)))))))))))) :pattern ((Prims.pow2.fuel_instrumented ZFuel @x0)) :qid lemma_FStar.Int.pow2_values)) :named lemma_FStar.Int.pow2_values))

; Lemma: FStar.Seq.Base.hasEq_lemma

;;; Fact-ids: Name FStar.Seq.Base.lemma_index_slice; Namespace FStar.Seq.Base

; Lemma: FStar.Seq.Base.lemma_index_upd1

;;; Fact-ids: Name FStar.Seq.Base.lemma_index_upd1; Namespace FStar.Seq.Base

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term)) (! (implies (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Seq.Base.seq @u0 @x1)) (HasType @x3 (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u0 @x1 @x2)) (HasType @x4 @x1)) (= (FStar.Seq.Base.index @u0 @x1 (FStar.Seq.Base.upd @u0 @x1 @x2 @x3 @x4) @x3) @x4)) :pattern ((FStar.Seq.Base.index @u0 @x1 (FStar.Seq.Base.upd @u0 @x1 @x2 @x3 @x4) @x3)) :qid lemma_FStar.Seq.Base.lemma_index_upd1)) :named lemma_FStar.Seq.Base.lemma_index_upd1))

; Lemma: FStar.Seq.Base.lemma_len_slice

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term)) (! (implies (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Seq.Base.seq @u0 @x1)) (HasType @x3 Prims.nat) (HasType @x4 (Tm_refine_ee3137b5d9f07244c499a05a59dd12e7 @u0 @x3 @x1 @x2))) (= (FStar.Seq.Base.length @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4)) (Prims.op_Minus @x4 @x3))) :pattern ((FStar.Seq.Base.length @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4))) :qid lemma_FStar.Seq.Base.lemma_len_slice)) :named lemma_FStar.Seq.Base.lemma_len_slice))

; Lemma: FStar.Seq.Base.lemma_len_upd

;;; Fact-ids: Name FStar.Seq.Base.lemma_len_upd; Namespace FStar.Seq.Base

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term)) (! (implies (and (HasType @x1 (Tm_type @u0)) (HasType @x2 Prims.nat) (HasType @x3 @x1) (HasType @x4 (Tm_refine_0817137556c8403efcddf9d82e1767c5 @u0 @x2 @x1))) (= (FStar.Seq.Base.length @u0 @x1 (FStar.Seq.Base.upd @u0 @x1 @x4 @x2 @x3)) (FStar.Seq.Base.length @u0 @x1 @x4))) :pattern ((FStar.Seq.Base.length @u0 @x1 (FStar.Seq.Base.upd @u0 @x1 @x4 @x2 @x3))) :qid lemma_FStar.Seq.Base.lemma_len_upd)) :named lemma_FStar.Seq.Base.lemma_len_upd))

; Lemma: FStar.Seq.Properties.lemma_tail_slice

;;; Fact-ids: Name FStar.Seq.Properties.lemma_tail_slice; Namespace FStar.Seq.Properties

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term)) (! (implies (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Seq.Base.seq @u0 @x1)) (HasType @x3 Prims.nat) (HasType @x4 (Tm_refine_c8cc915fa69008ea6ec6c900835be1d5 @u0 @x3 @x1 @x2))) (= (FStar.Seq.Properties.tail @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4)) (FStar.Seq.Base.slice @u0 @x1 @x2 (Prims.op_Plus @x3 (BoxInt 1)) @x4))) :pattern ((FStar.Seq.Properties.tail @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4))) :qid lemma_FStar.Seq.Properties.lemma_tail_slice)) :named lemma_FStar.Seq.Properties.lemma_tail_slice))

; Lemma: FStar.SizeT.fits_at_least_16

;;; Fact-ids: Name FStar.SizeT.fits_at_least_16; Namespace FStar.SizeT

(assert (! (forall ((@x0 Term)) (! (implies (and (HasType @x0 Prims.nat) (<= (BoxInt_proj_0 (BoxInt 0)) (BoxInt_proj_0 @x0)) (< (BoxInt_proj_0 @x0) (BoxInt_proj_0 (Prims.pow2.fuel_instrumented ZFuel (BoxInt 16))))) (Valid (FStar.SizeT.fits @x0))) :pattern ((FStar.SizeT.fits @x0)) :qid lemma_FStar.SizeT.fits_at_least_16)) :named lemma_FStar.SizeT.fits_at_least_16))

; Lemma: FStar.SizeT.size_uint_to_t_inj

;;; Fact-ids: Name Pulse.Lib.InsertionSort.slice_index; Namespace Pulse.Lib.InsertionSort

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term)) (! (implies (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Seq.Base.seq @u0 @x1)) (HasType @x3 Prims.nat) (HasType @x4 Prims.nat) (HasType @x5 Prims.nat) (<= (BoxInt_proj_0 @x3) (BoxInt_proj_0 @x4)) (< (BoxInt_proj_0 @x4) (BoxInt_proj_0 @x5)) (<= (BoxInt_proj_0 @x5) (BoxInt_proj_0 (FStar.Seq.Base.length @u0 @x1 @x2)))) (= (FStar.Seq.Base.index @u0 @x1 @x2 @x4) (FStar.Seq.Base.index @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x5) (Prims.op_Minus @x4 @x3)))) :pattern ((FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x5) (FStar.Seq.Base.index @u0 @x1 @x2 @x4)) :qid lemma_Pulse.Lib.InsertionSort.slice_index)) :named lemma_Pulse.Lib.InsertionSort.slice_index))

;;; Fact-ids: Name Pulse.Lib.InsertionSort.upd_count; Namespace Pulse.Lib.InsertionSort

(assert (! (forall ((@x0 Term)) (! (= (Prims.not @x0) (BoxBool (not (BoxBool_proj_0 @x0)))) :pattern ((Prims.not @x0)) :qid primitive_Prims.not)) :named primitive_Prims.not))

;;; Fact-ids: Name Prims.op_Equals; Namespace Prims

(assert (! (forall ((@x0 Term) (@x1 Term) (@x2 Term)) (! (= (Prims.op_Equals @x0 @x1 @x2) (BoxBool (= @x1 @x2))) :pattern ((Prims.op_Equals @x0 @x1 @x2)) :qid primitive_Prims.op_Equals)) :named primitive_Prims.op_Equals))

;;; Fact-ids: Name Prims.op_Greater; Namespace Prims

(assert (! (forall ((@x0 Term) (@x1 Term)) (! (= (Prims.op_Greater @x0 @x1) (BoxBool (> (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1)))) :pattern ((Prims.op_Greater @x0 @x1)) :qid primitive_Prims.op_Greater)) :named primitive_Prims.op_Greater))

;;; Fact-ids: Name Prims.op_Greater_Equals; Namespace Prims

(assert (! (forall ((@x0 Term) (@x1 Term)) (! (= (Prims.op_Greater_Equals @x0 @x1) (BoxBool (>= (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1)))) :pattern ((Prims.op_Greater_Equals @x0 @x1)) :qid primitive_Prims.op_Greater_Equals)) :named primitive_Prims.op_Greater_Equals))

;;; Fact-ids: Name Prims.op_Less; Namespace Prims

(assert (! (forall ((@x0 Term) (@x1 Term)) (! (= (Prims.op_Less @x0 @x1) (BoxBool (< (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1)))) :pattern ((Prims.op_Less @x0 @x1)) :qid primitive_Prims.op_Less)) :named primitive_Prims.op_Less))

;;; Fact-ids: Name Prims.op_Less_Equals; Namespace Prims

(assert (! (forall ((@x0 Term) (@x1 Term)) (! (= (Prims.op_Less_Equals @x0 @x1) (BoxBool (<= (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1)))) :pattern ((Prims.op_Less_Equals @x0 @x1)) :qid primitive_Prims.op_Less_Equals)) :named primitive_Prims.op_Less_Equals))

;;; Fact-ids: Name Prims.op_Less_Greater; Namespace Prims

;;; Fact-ids: Name Prims.op_Minus; Namespace Prims

(assert (! (forall ((@x0 Term) (@x1 Term)) (! (= (Prims.op_Minus @x0 @x1) (BoxInt (- (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1)))) :pattern ((Prims.op_Minus @x0 @x1)) :qid primitive_Prims.op_Minus)) :named primitive_Prims.op_Minus))

;;; Fact-ids: Name Prims.op_Plus; Namespace Prims

(assert (! (forall ((@x0 Term) (@x1 Term)) (! (= (Prims.op_Plus @x0 @x1) (BoxInt (+ (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1)))) :pattern ((Prims.op_Plus @x0 @x1)) :qid primitive_Prims.op_Plus)) :named primitive_Prims.op_Plus))

;;; Fact-ids: Name Prims.op_Star; Namespace Prims

; Projector equation

;;; Fact-ids: Name Pulse.Lib.TotalOrder.__proj__Mktotal_order__item__compare; Namespace Pulse.Lib.TotalOrder

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term)) (! (= (Pulse.Lib.TotalOrder.__proj__Mktotal_order__item__compare @u0 @x1 @x2) (Pulse.Lib.TotalOrder.Mktotal_order_@compare @x2)) :pattern ((Pulse.Lib.TotalOrder.__proj__Mktotal_order__item__compare @u0 @x1 @x2)) :qid proj_equation_Pulse.Lib.TotalOrder.Mktotal_order_@compare)) :named proj_equation_Pulse.Lib.TotalOrder.Mktotal_order_@compare))
(assert (! (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term)) (! (iff (HasTypeFuel @u0 @x1 (Tm_refine_0817137556c8403efcddf9d82e1767c5 @u2 @x3 @x4)) (and (HasTypeFuel @u0 @x1 (FStar.Seq.Base.seq @u2 @x4)) (< (BoxInt_proj_0 @x3) (BoxInt_proj_0 (FStar.Seq.Base.length @u2 @x4 @x1))))) :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_0817137556c8403efcddf9d82e1767c5 @u2 @x3 @x4))) :qid refinement_interpretation_Tm_refine_0817137556c8403efcddf9d82e1767c5)) :named refinement_interpretation_Tm_refine_0817137556c8403efcddf9d82e1767c5))

; refinement_interpretation

;;; Fact-ids: Name FStar.Seq.Base.empty; Namespace FStar.Seq.Base

; refinement_interpretation

(assert (! (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term)) (! (iff (HasTypeFuel @u0 @x1 (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u2 @x3 @x4)) (and (HasTypeFuel @u0 @x1 Prims.nat) (< (BoxInt_proj_0 @x1) (BoxInt_proj_0 (FStar.Seq.Base.length @u2 @x3 @x4))))) :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u2 @x3 @x4))) :qid refinement_interpretation_Tm_refine_160fe7faad9a466b3cae8455bac5be60)) :named refinement_interpretation_Tm_refine_160fe7faad9a466b3cae8455bac5be60))

; refinement_interpretation

;;; Fact-ids: Name FStar.Seq.Properties.seq_find_aux; Namespace FStar.Seq.Properties

;;; Fact-ids: Name FStar.SizeT.uint_to_t; Namespace FStar.SizeT

(assert (! (forall ((@u0 Fuel) (@x1 Term) (@x2 Term)) (! (iff (HasTypeFuel @u0 @x1 (Tm_refine_207024d2522be2ff59992eb07d6dc785 @x2)) (and (HasTypeFuel @u0 @x1 (FStar.SizeT.t Dummy_value)) (= (FStar.SizeT.v @x1) @x2))) :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_207024d2522be2ff59992eb07d6dc785 @x2))) :qid refinement_interpretation_Tm_refine_207024d2522be2ff59992eb07d6dc785)) :named refinement_interpretation_Tm_refine_207024d2522be2ff59992eb07d6dc785))
(assert (! (forall ((@u0 Fuel) (@x1 Term) (@x2 Term)) (! (iff (HasTypeFuel @u0 @x1 (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x2)) (and (HasTypeFuel @u0 @x1 Prims.unit) (Valid @x2))) :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x2))) :qid refinement_interpretation_Tm_refine_2de20c066034c13bf76e9c0b94f4806c)) :named refinement_interpretation_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))

; refinement_interpretation

;;; Fact-ids: Name FStar.Seq.Properties.slice_slice; Namespace FStar.Seq.Properties

; refinement_interpretation

;;; Fact-ids: Name Prims.nat; Namespace Prims

(assert (! (forall ((@u0 Fuel) (@x1 Term)) (! (iff (HasTypeFuel @u0 @x1 Tm_refine_542f9d4f129664613f2483a6c88bc7c2) (and (HasTypeFuel @u0 @x1 Prims.int) (>= (BoxInt_proj_0 @x1) (BoxInt_proj_0 (BoxInt 0))))) :pattern ((HasTypeFuel @u0 @x1 Tm_refine_542f9d4f129664613f2483a6c88bc7c2)) :qid refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2)) :named refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2))

; refinement_interpretation

;;; Fact-ids: Name FStar.SizeT.lt; Namespace FStar.SizeT

(assert (! (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term)) (! (iff (HasTypeFuel @u0 @x1 (Tm_refine_5add1adb79e75abb939ada4dd8a7538f @x2 @x3)) (and (HasTypeFuel @u0 @x1 Prims.bool) (= @x1 (Prims.op_Less (FStar.SizeT.v @x2) (FStar.SizeT.v @x3))))) :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_5add1adb79e75abb939ada4dd8a7538f @x2 @x3))) :qid refinement_interpretation_Tm_refine_5add1adb79e75abb939ada4dd8a7538f)) :named refinement_interpretation_Tm_refine_5add1adb79e75abb939ada4dd8a7538f))

; refinement_interpretation

;;; Fact-ids: Name FStar.Seq.Base.lemma_index_upd2; Namespace FStar.Seq.Base

(assert (! (forall ((@u0 Fuel) (@x1 Term)) (! (iff (HasTypeFuel @u0 @x1 Tm_refine_7df43cb9feb536df62477b7b30ce1682) (and (HasTypeFuel @u0 @x1 Prims.nat) (Valid (FStar.SizeT.fits @x1)))) :pattern ((HasTypeFuel @u0 @x1 Tm_refine_7df43cb9feb536df62477b7b30ce1682)) :qid refinement_interpretation_Tm_refine_7df43cb9feb536df62477b7b30ce1682)) :named refinement_interpretation_Tm_refine_7df43cb9feb536df62477b7b30ce1682))

; refinement_interpretation

;;; Fact-ids: Name FStar.SizeT.sub; Namespace FStar.SizeT

(assert (! (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term)) (! (iff (HasTypeFuel @u0 @x1 (Tm_refine_89f93f0d2f57e09801995b3283389610 @x2 @x3)) (and (HasTypeFuel @u0 @x1 (FStar.SizeT.t Dummy_value)) (= (FStar.SizeT.v @x1) (Prims.op_Minus (FStar.SizeT.v @x2) (FStar.SizeT.v @x3))))) :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_89f93f0d2f57e09801995b3283389610 @x2 @x3))) :qid refinement_interpretation_Tm_refine_89f93f0d2f57e09801995b3283389610)) :named refinement_interpretation_Tm_refine_89f93f0d2f57e09801995b3283389610))
(assert (! (forall ((@u0 Fuel) (@x1 Term)) (! (iff (HasTypeFuel @u0 @x1 Tm_refine_9d6af3f3535473623f7aec2f0501897f) (and (HasTypeFuel @u0 @x1 (Tm_type U_zero)) (Valid (Prims.hasEq U_zero @x1)))) :pattern ((HasTypeFuel @u0 @x1 Tm_refine_9d6af3f3535473623f7aec2f0501897f)) :qid refinement_interpretation_Tm_refine_9d6af3f3535473623f7aec2f0501897f)) :named refinement_interpretation_Tm_refine_9d6af3f3535473623f7aec2f0501897f))

; refinement_interpretation

;;; Fact-ids: Name FStar.Seq.Properties.head; Namespace FStar.Seq.Properties

;;; Fact-ids: Name FStar.Seq.Base.lemma_index_slice; Namespace FStar.Seq.Base

; refinement_interpretation

;;; Fact-ids: Name FStar.Seq.Properties.lemma_tail_slice; Namespace FStar.Seq.Properties

(assert (! (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term)) (! (iff (HasTypeFuel @u0 @x1 (Tm_refine_c8cc915fa69008ea6ec6c900835be1d5 @u2 @x3 @x4 @x5)) (and (HasTypeFuel @u0 @x1 Prims.nat) (BoxBool_proj_0 (Prims.op_Less @x3 @x1)) (BoxBool_proj_0 (Prims.op_Less_Equals @x1 (FStar.Seq.Base.length @u2 @x4 @x5))))) :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_c8cc915fa69008ea6ec6c900835be1d5 @u2 @x3 @x4 @x5))) :qid refinement_interpretation_Tm_refine_c8cc915fa69008ea6ec6c900835be1d5)) :named refinement_interpretation_Tm_refine_c8cc915fa69008ea6ec6c900835be1d5))

; refinement_interpretation

;;; Fact-ids: Name FStar.Seq.Base.lemma_index_slice; Namespace FStar.Seq.Base

; refinement_interpretation

;;; Fact-ids: Name Pulse.Lib.InsertionSort.ordered; Namespace Pulse.Lib.InsertionSort

(assert (! (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term)) (! (iff (HasTypeFuel @u0 @x1 (Tm_refine_cc0abff8026303d2626cb79040e5c59e @u2 @x3 @x4)) (and (HasTypeFuel @u0 @x1 Prims.int) (>= (BoxInt_proj_0 @x1) (BoxInt_proj_0 (BoxInt 0))) (< (BoxInt_proj_0 @x1) (BoxInt_proj_0 (FStar.Seq.Base.length @u2 @x3 @x4))))) :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_cc0abff8026303d2626cb79040e5c59e @u2 @x3 @x4))) :qid refinement_interpretation_Tm_refine_cc0abff8026303d2626cb79040e5c59e)) :named refinement_interpretation_Tm_refine_cc0abff8026303d2626cb79040e5c59e))

;;; Fact-ids: Name Pulse.Lib.Array.Core.elseq; Namespace Pulse.Lib.Array.Core

(assert (! (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term)) (! (iff (HasTypeFuel @u0 @x1 (Tm_refine_cf7cf1886ab56e79bff605f06a0f72bc @u2 @x3 @x4)) (and (HasTypeFuel @u0 @x1 (FStar.Ghost.erased @u2 (FStar.Seq.Base.seq @u2 @x3))) (= (FStar.Seq.Base.length @u2 @x3 (FStar.Ghost.reveal @u2 (FStar.Seq.Base.seq @u2 @x3) @x1)) (FStar.SizeT.v @x4)))) :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_cf7cf1886ab56e79bff605f06a0f72bc @u2 @x3 @x4))) :qid refinement_interpretation_Tm_refine_cf7cf1886ab56e79bff605f06a0f72bc)) :named refinement_interpretation_Tm_refine_cf7cf1886ab56e79bff605f06a0f72bc))

; refinement_interpretation

;;; Fact-ids: Name Pulse.Lib.TotalOrder.total_order; Namespace Pulse.Lib.TotalOrder; Name Pulse.Lib.TotalOrder.Mktotal_order; Namespace Pulse.Lib.TotalOrder

(assert (! (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term)) (! (iff (HasTypeFuel @u0 @x1 (Tm_refine_d7ac964e93ed768e3b6dc5dc2457c982 @u2 @x3 @x4)) (and (HasTypeFuel @u0 @x1 Prims.unit) (forall ((@x5 Term) (@x6 Term)) (! (implies (and (HasType @x5 @x3) (HasType @x6 @x3)) (iff (BoxBool_proj_0 (FStar.Order.eq (ApplyTT (ApplyTT @x4 @x5) @x6))) (= @x5 @x6))) :pattern ((ApplyTT (ApplyTT @x4 @x5) @x6)) :qid refinement_interpretation_Tm_refine_d7ac964e93ed768e3b6dc5dc2457c982.1)) (forall ((@x5 Term) (@x6 Term) (@x7 Term)) (! (implies (and (HasType @x5 @x3) (HasType @x6 @x3) (HasType @x7 @x3) (BoxBool_proj_0 (FStar.Order.lt (ApplyTT (ApplyTT @x4 @x5) @x6))) (BoxBool_proj_0 (FStar.Order.lt (ApplyTT (ApplyTT @x4 @x6) @x7)))) (BoxBool_proj_0 (FStar.Order.lt (ApplyTT (ApplyTT @x4 @x5) @x7)))) :pattern ((ApplyTT (ApplyTT @x4 @x5) @x6) (ApplyTT (ApplyTT @x4 @x6) @x7)) :qid refinement_interpretation_Tm_refine_d7ac964e93ed768e3b6dc5dc2457c982.2)) (forall ((@x5 Term) (@x6 Term)) (! (implies (and (HasType @x5 @x3) (HasType @x6 @x3)) (= (ApplyTT (ApplyTT @x4 @x5) @x6) (Pulse.Lib.TotalOrder.flip_order (ApplyTT (ApplyTT @x4 @x6) @x5)))) :pattern ((ApplyTT (ApplyTT @x4 @x5) @x6)) :qid refinement_interpretation_Tm_refine_d7ac964e93ed768e3b6dc5dc2457c982.3)))) :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_d7ac964e93ed768e3b6dc5dc2457c982 @u2 @x3 @x4))) :qid refinement_interpretation_Tm_refine_d7ac964e93ed768e3b6dc5dc2457c982)) :named refinement_interpretation_Tm_refine_d7ac964e93ed768e3b6dc5dc2457c982))

; refinement_interpretation

;;; Fact-ids: Name FStar.Seq.Base.slice; Namespace FStar.Seq.Base

(assert (! (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term)) (! (iff (HasTypeFuel @u0 @x1 (Tm_refine_ee3137b5d9f07244c499a05a59dd12e7 @u2 @x3 @x4 @x5)) (and (HasTypeFuel @u0 @x1 Prims.nat) (BoxBool_proj_0 (Prims.op_Less_Equals @x3 @x1)) (BoxBool_proj_0 (Prims.op_Less_Equals @x1 (FStar.Seq.Base.length @u2 @x4 @x5))))) :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_ee3137b5d9f07244c499a05a59dd12e7 @u2 @x3 @x4 @x5))) :qid refinement_interpretation_Tm_refine_ee3137b5d9f07244c499a05a59dd12e7)) :named refinement_interpretation_Tm_refine_ee3137b5d9f07244c499a05a59dd12e7))

; refinement kinding

;;; Fact-ids: Name FStar.Seq.Base.lemma_len_upd; Namespace FStar.Seq.Base

;;; Fact-ids: Name Pulse.Lib.InsertionSort.count; Namespace Pulse.Lib.InsertionSort

;;; Fact-ids: Name Pulse.Lib.TotalOrder.total_order; Namespace Pulse.Lib.TotalOrder; Name Pulse.Lib.TotalOrder.Mktotal_order; Namespace Pulse.Lib.TotalOrder

; free var typing

;;; Fact-ids: Name FStar.Ghost.erased; Namespace FStar.Ghost

(assert (! (forall ((@u0 Universe) (@x1 Term)) (! (implies (HasType @x1 (Tm_type @u0)) (HasType (FStar.Ghost.erased @u0 @x1) (Tm_type @u0))) :pattern ((FStar.Ghost.erased @u0 @x1)) :qid typing_FStar.Ghost.erased)) :named typing_FStar.Ghost.erased))

; free var typing

;;; Fact-ids: Name FStar.Ghost.hide; Namespace FStar.Ghost

; free var typing

;;; Fact-ids: Name FStar.Ghost.reveal; Namespace FStar.Ghost

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term)) (! (implies (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Ghost.erased @u0 @x1))) (HasType (FStar.Ghost.reveal @u0 @x1 @x2) @x1)) :pattern ((FStar.Ghost.reveal @u0 @x1 @x2)) :qid typing_FStar.Ghost.reveal)) :named typing_FStar.Ghost.reveal))

; free var typing

;;; Fact-ids: Name FStar.Seq.Base.empty; Namespace FStar.Seq.Base

; free var typing

;;; Fact-ids: Name FStar.Seq.Base.index; Namespace FStar.Seq.Base

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term)) (! (implies (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Seq.Base.seq @u0 @x1)) (HasType @x3 (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u0 @x1 @x2))) (HasType (FStar.Seq.Base.index @u0 @x1 @x2 @x3) @x1)) :pattern ((FStar.Seq.Base.index @u0 @x1 @x2 @x3)) :qid typing_FStar.Seq.Base.index)) :named typing_FStar.Seq.Base.index))

; free var typing

; free var typing

;;; Fact-ids: Name FStar.Seq.Base.seq; Namespace FStar.Seq.Base

(assert (! (forall ((@u0 Universe) (@x1 Term)) (! (implies (HasType @x1 (Tm_type @u0)) (HasType (FStar.Seq.Base.seq @u0 @x1) (Tm_type @u0))) :pattern ((FStar.Seq.Base.seq @u0 @x1)) :qid typing_FStar.Seq.Base.seq)) :named typing_FStar.Seq.Base.seq))

; free var typing

;;; Fact-ids: Name FStar.Seq.Base.slice; Namespace FStar.Seq.Base

(assert (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term)) (! (implies (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Seq.Base.seq @u0 @x1)) (HasType @x3 Prims.nat) (HasType @x4 (Tm_refine_ee3137b5d9f07244c499a05a59dd12e7 @u0 @x3 @x1 @x2))) (HasType (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4) (FStar.Seq.Base.seq @u0 @x1))) :pattern ((FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4)) :qid typing_FStar.Seq.Base.slice)) :named typing_FStar.Seq.Base.slice))

; free var typing

;;; Fact-ids: Name FStar.Seq.Base.upd; Namespace FStar.Seq.Base

; free var typing

;;; Fact-ids: Name FStar.Seq.Properties.head; Namespace FStar.Seq.Properties

;;; Fact-ids: Name FStar.SizeT.lt; Namespace FStar.SizeT

(assert (! (forall ((@x0 Term) (@x1 Term)) (! (implies (and (HasType @x0 (FStar.SizeT.t Dummy_value)) (HasType @x1 (FStar.SizeT.t Dummy_value))) (HasType (FStar.SizeT.lt @x0 @x1) (Tm_refine_5add1adb79e75abb939ada4dd8a7538f @x0 @x1))) :pattern ((FStar.SizeT.lt @x0 @x1)) :qid typing_FStar.SizeT.lt)) :named typing_FStar.SizeT.lt))
(assert (! (forall ((@x0 Term) (@x1 Term) (@x2 Term)) (! (implies (and (HasType @x0 (FStar.SizeT.t Dummy_value)) (HasType @x1 (FStar.SizeT.t Dummy_value)) (HasType @x2 (Prims.squash (Prims.b2t (Prims.op_Greater_Equals (FStar.SizeT.v @x0) (FStar.SizeT.v @x1)))))) (HasType (FStar.SizeT.sub @x0 @x1 @x2) (Tm_refine_89f93f0d2f57e09801995b3283389610 @x0 @x1))) :pattern ((FStar.SizeT.sub @x0 @x1 @x2)) :qid typing_FStar.SizeT.sub)) :named typing_FStar.SizeT.sub))

; free var typing

;;; Fact-ids: Name FStar.SizeT.t; Namespace FStar.SizeT

(assert (! (forall ((@u0 Dummy_sort)) (! (HasType (FStar.SizeT.t @u0) Prims.eqtype) :pattern ((FStar.SizeT.t @u0)) :qid typing_FStar.SizeT.t)) :named typing_FStar.SizeT.t))

; free var typing

;;; Fact-ids: Name FStar.SizeT.uint_to_t; Namespace FStar.SizeT

(assert (! (forall ((@x0 Term) (@x1 Term)) (! (implies (and (HasType @x0 Prims.int) (HasType @x1 (Prims.squash (FStar.SizeT.fits @x0)))) (HasType (FStar.SizeT.uint_to_t @x0 @x1) (Tm_refine_207024d2522be2ff59992eb07d6dc785 @x0))) :pattern ((FStar.SizeT.uint_to_t @x0 @x1)) :qid typing_FStar.SizeT.uint_to_t)) :named typing_FStar.SizeT.uint_to_t))

; free var typing

(assert (! (forall ((@x0 Term)) (! (implies (HasType @x0 (FStar.SizeT.t Dummy_value)) (HasType (FStar.SizeT.v @x0) Tm_refine_7df43cb9feb536df62477b7b30ce1682)) :pattern ((FStar.SizeT.v @x0)) :qid typing_FStar.SizeT.v)) :named typing_FStar.SizeT.v))

;;; Fact-ids: Name FStar.Order.order; Namespace FStar.Order; Name FStar.Order.Lt; Namespace FStar.Order; Name FStar.Order.Eq; Namespace FStar.Order; Name FStar.Order.Gt; Namespace FStar.Order

; unit inversion

;;; Fact-ids: Name Prims.unit; Namespace Prims

(assert (! (forall ((@u0 Fuel) (@x1 Term)) (! (implies (HasTypeFuel @u0 @x1 Prims.unit) (= @x1 Tm_unit)) :pattern ((HasTypeFuel @u0 @x1 Prims.unit)) :qid unit_inversion)) :named unit_inversion))

; unit typing

; Starting query at Pulse.Lib.InsertionSort.fst(177,10-178,25)

; universe local constant

(declare-fun a () Universe)
(declare-fun Tm_refine_2931766ea5bf456093e90a5392e0fd4e (Universe Term Term Term Term Term Term) Term)

;;; Fact-ids: 

(assert (! (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term)) (! (iff (HasTypeFuel @u0 @x1 (Tm_refine_2931766ea5bf456093e90a5392e0fd4e @u2 @x3 @x4 @x5 @x6 @x7 @x8)) (and (HasTypeFuel @u0 @x1 Prims.unit) (<= (BoxInt_proj_0 (BoxInt 1)) (BoxInt_proj_0 (FStar.SizeT.v (FStar.Ghost.reveal U_zero (FStar.SizeT.t Dummy_value) (FStar.Ghost.reveal U_zero (FStar.Ghost.erased U_zero (FStar.SizeT.t Dummy_value)) @x3))))) (<= (BoxInt_proj_0 (FStar.SizeT.v (FStar.Ghost.reveal U_zero (FStar.SizeT.t Dummy_value) (FStar.Ghost.reveal U_zero (FStar.Ghost.erased U_zero (FStar.SizeT.t Dummy_value)) @x3)))) (BoxInt_proj_0 (FStar.SizeT.v @x4))) (= (FStar.Seq.Base.length @u2 @x5 (FStar.Ghost.reveal @u2 (FStar.Seq.Base.seq @u2 @x5) (FStar.Ghost.reveal @u2 (FStar.Ghost.erased @u2 (FStar.Seq.Base.seq @u2 @x5)) @x6))) (FStar.Seq.Base.length @u2 @x5 (FStar.Ghost.reveal @u2 (FStar.Seq.Base.seq @u2 @x5) @x7))) (Valid (Pulse.Lib.InsertionSort.sorted @u2 @x5 @x8 (FStar.Seq.Base.slice @u2 @x5 (FStar.Ghost.reveal @u2 (FStar.Seq.Base.seq @u2 @x5) (FStar.Ghost.reveal @u2 (FStar.Ghost.erased @u2 (FStar.Seq.Base.seq @u2 @x5)) @x6)) (BoxInt 0) (FStar.SizeT.v (FStar.Ghost.reveal U_zero (FStar.SizeT.t Dummy_value) (FStar.Ghost.reveal U_zero (FStar.Ghost.erased U_zero (FStar.SizeT.t Dummy_value)) @x3)))))) (Valid (Pulse.Lib.InsertionSort.permutation @u2 @x5 @x8 (FStar.Ghost.reveal @u2 (FStar.Seq.Base.seq @u2 @x5) @x7) (FStar.Ghost.reveal @u2 (FStar.Seq.Base.seq @u2 @x5) (FStar.Ghost.reveal @u2 (FStar.Ghost.erased @u2 (FStar.Seq.Base.seq @u2 @x5)) @x6)))))) :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_2931766ea5bf456093e90a5392e0fd4e @u2 @x3 @x4 @x5 @x6 @x7 @x8))) :qid refinement_interpretation_Tm_refine_2931766ea5bf456093e90a5392e0fd4e)) :named refinement_interpretation_Tm_refine_2931766ea5bf456093e90a5392e0fd4e))

; haseq for Tm_refine_2931766ea5bf456093e90a5392e0fd4e

(declare-fun Tm_refine_ed6f48d81446efd270ff7f730c426736 (Term Term) Term)

;;; Fact-ids: 

; refinement_interpretation

;;; Fact-ids: 

(assert (! (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term)) (! (iff (HasTypeFuel @u0 @x1 (Tm_refine_ed6f48d81446efd270ff7f730c426736 @x2 @x3)) (and (HasTypeFuel @u0 @x1 Prims.unit) (= (BoxBool true) (FStar.SizeT.lt (FStar.Ghost.reveal U_zero (FStar.SizeT.t Dummy_value) (FStar.Ghost.reveal U_zero (FStar.Ghost.erased U_zero (FStar.SizeT.t Dummy_value)) @x2)) @x3)))) :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_ed6f48d81446efd270ff7f730c426736 @x2 @x3))) :qid refinement_interpretation_Tm_refine_ed6f48d81446efd270ff7f730c426736)) :named refinement_interpretation_Tm_refine_ed6f48d81446efd270ff7f730c426736))

;; push{0

(declare-fun @sk_1 () Term)
(declare-fun @sk_2 () Term)
(declare-fun @sk_3 () Term)
(declare-fun @sk_4 () Term)
(declare-fun @sk_5 () Term)
(declare-fun @sk_6 () Term)
(declare-fun @sk_7 () Term)
(declare-fun @sk_8 () Term)
(declare-fun @sk_9 () Term)
(declare-fun @sk_10 () Term)
(declare-fun @sk_11 () Term)
(declare-fun @sk_13 () Term)
(assert (! (HasType @sk_1 (Tm_type a)) :named @hypothesis_23))

;;; Fact-ids: 

(assert (! (HasType @sk_2 (Pulse.Lib.TotalOrder.total_order a @sk_1)) :named @hypothesis_24))

;;; Fact-ids: 

;;; Fact-ids: 

(assert (! (HasType @sk_4 (FStar.SizeT.t Dummy_value)) :named @hypothesis_26))
(assert (! (HasType @sk_5 (Tm_refine_cf7cf1886ab56e79bff605f06a0f72bc a @sk_1 @sk_4)) :named @hypothesis_27))

;;; Fact-ids: 

(assert (! (HasType @sk_6 (Prims.squash (Prims.b2t (Prims.op_Greater (FStar.SizeT.v @sk_4) (BoxInt 0))))) :named @hypothesis_28))

;;; Fact-ids: 

;;; Fact-ids: 

;;; Fact-ids: 

(assert (! (HasType @sk_9 (FStar.Ghost.erased U_zero (FStar.Ghost.erased U_zero (FStar.SizeT.t Dummy_value)))) :named @hypothesis_31))

;;; Fact-ids: 

(assert (! (HasType @sk_10 (FStar.Ghost.erased a (FStar.Ghost.erased a (FStar.Seq.Base.seq a @sk_1)))) :named @hypothesis_32))

;;; Fact-ids: 

(assert (! (HasType @sk_11 (Tm_refine_2931766ea5bf456093e90a5392e0fd4e a @sk_9 @sk_4 @sk_1 @sk_10 @sk_5 @sk_2)) :named @hypothesis_33))
(assert (! (HasType @sk_13 (Tm_refine_ed6f48d81446efd270ff7f730c426736 @sk_9 @sk_4)) :named @hypothesis_35))

;;; Fact-ids: 

(push)

;;; Fact-ids: 

(assert (! (= MaxFuel (SFuel (SFuel (SFuel (SFuel (SFuel (SFuel (SFuel (SFuel ZFuel))))))))) :named @MaxFuel_assumption))
(assert (! (= MaxIFuel (SFuel (SFuel ZFuel))) :named @MaxIFuel_assumption))

; query

(assert (! (not (Valid (Pulse.Lib.InsertionSort.inner_invariant a @sk_1 @sk_2 (FStar.Ghost.reveal a (FStar.Seq.Base.seq a @sk_1) (FStar.Ghost.reveal a (FStar.Ghost.erased a (FStar.Seq.Base.seq a @sk_1)) @sk_10)) (FStar.Ghost.reveal a (FStar.Seq.Base.seq a @sk_1) (FStar.Ghost.reveal a (FStar.Ghost.erased a (FStar.Seq.Base.seq a @sk_1)) @sk_10)) (FStar.Seq.Base.index a @sk_1 (FStar.Ghost.reveal a (FStar.Seq.Base.seq a @sk_1) (FStar.Ghost.reveal a (FStar.Ghost.erased a (FStar.Seq.Base.seq a @sk_1)) @sk_10)) (FStar.SizeT.v (FStar.Ghost.reveal U_zero (FStar.SizeT.t Dummy_value) (FStar.Ghost.reveal U_zero (FStar.Ghost.erased U_zero (FStar.SizeT.t Dummy_value)) @sk_9)))) (FStar.SizeT.sub (FStar.Ghost.reveal U_zero (FStar.SizeT.t Dummy_value) (FStar.Ghost.reveal U_zero (FStar.Ghost.erased U_zero (FStar.SizeT.t Dummy_value)) @sk_9)) (FStar.SizeT.uint_to_t (BoxInt 1) Tm_unit) Tm_unit) (FStar.Ghost.reveal U_zero (FStar.SizeT.t Dummy_value) (FStar.Ghost.reveal U_zero (FStar.Ghost.erased U_zero (FStar.SizeT.t Dummy_value)) @sk_9)) (BoxBool false)))) :named @query))
(set-option :rlimit 2000000)
(check-sat)
