(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :auto_config false)
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
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.qi.cost "(+ weight generation)")
(set-option :type-check true)
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

(declare-fun Ctor (T@T) Int)
(declare-fun intType () T@T)
(declare-fun boolType () T@T)
(declare-fun int_2_U (Int) T@U)
(declare-fun U_2_int (T@U) Int)
(declare-fun type (T@U) T@T)
(declare-fun bool_2_U (Bool) T@U)
(declare-fun U_2_bool (T@U) Bool)
(declare-fun PermissionComponentType () T@T)
(declare-fun perm$R () T@U)
(declare-fun perm$N () T@U)
(declare-fun FieldType (T@T) T@T)
(declare-fun FieldTypeInv0 (T@T) T@T)
(declare-fun joinable () T@U)
(declare-fun TypeNameType () T@T)
(declare-fun |token#t| () T@U)
(declare-fun forkK () T@U)
(declare-fun MuType () T@T)
(declare-fun mu () T@U)
(declare-fun held () T@U)
(declare-fun rdheld () T@U)
(declare-fun |Node#t| () T@U)
(declare-fun ModuleNameType () T@T)
(declare-fun |module#default| () T@U)
(declare-fun refType () T@T)
(declare-fun Node.next () T@U)
(declare-fun Node.value () T@U)
(declare-fun Node.valid () T@U)
(declare-fun Permission$denominator () Int)
(declare-fun MapType0Type (T@T T@T) T@T)
(declare-fun MapType0TypeInv0 (T@T) T@T)
(declare-fun MapType0TypeInv1 (T@T) T@T)
(declare-fun MapType0Select (T@U T@U) T@U)
(declare-fun MapType0Store (T@U T@U T@U) T@U)
(declare-fun Permission$Zero () T@U)
(declare-fun Permission$Full () T@U)
(declare-fun Permission$FullFraction () Int)
(declare-fun MapType1Type (T@T T@T) T@T)
(declare-fun MapType1TypeInv0 (T@T) T@T)
(declare-fun MapType1TypeInv1 (T@T) T@T)
(declare-fun MapType1Select (T@U T@U T@U) T@U)
(declare-fun MapType1Store (T@U T@U T@U T@U) T@U)
(declare-fun ZeroMask () T@U)
(declare-fun IsGoodMask (T@U) Bool)
(declare-fun NonPredicateField (T@U) Bool)
(declare-fun Fractions (Int) Int)
(declare-fun channelK () Int)
(declare-fun monitorK () Int)
(declare-fun predicateK () Int)
(declare-fun PartialHeapTypeType () T@T)
(declare-fun combine (T@U T@U) T@U)
(declare-fun IsGoodState (T@U) Bool)
(declare-fun emptyPartialHeap () T@U)
(declare-fun MuBelow (T@U T@U) Bool)
(declare-fun $LockBottom () T@U)
(declare-fun MapType2Type (T@T) T@T)
(declare-fun MapType2TypeInv0 (T@T) T@T)
(declare-fun MapType2Select (T@U T@U T@U) T@U)
(declare-fun MapType2Store (T@U T@U T@U T@U) T@U)
(declare-fun IsGoodInhaleState (T@U T@U T@U T@U) Bool)
(declare-fun CanRead (T@U T@U T@U T@U) Bool)
(declare-fun IsGoodExhaleState (T@U T@U T@U T@U) Bool)
(declare-fun PredicateField (T@U) Bool)
(declare-fun CanReadForSure (T@U T@U T@U) Bool)
(declare-fun CanWrite (T@U T@U T@U) Bool)
(declare-fun wf (T@U T@U T@U) Bool)
(declare-fun DecPerm (T@U T@U T@U Int) T@U)
(declare-fun q@ite (Bool T@U T@U) T@U)
(declare-fun DecEpsilons (T@U T@U T@U Int) T@U)
(declare-fun IncPerm (T@U T@U T@U Int) T@U)
(declare-fun IncEpsilons (T@U T@U T@U Int) T@U)
(declare-fun Havocing (T@U T@U T@U T@U) T@U)
(declare-fun EmptyMask (T@U) Bool)
(declare-fun ZeroCredits () T@U)
(declare-fun null () T@U)
(declare-fun EmptyCredits (T@U) Bool)
(declare-fun submask (T@U T@U) Bool)
(declare-fun CurrentModule () T@U)
(declare-fun |#Node.at#limited#trigger| (T@U Int) Bool)
(declare-fun |#Node.valid#trigger| (T@U) Bool)
(declare-fun |#Node.at| (T@U T@U Int) Int)
(declare-fun |#Node.size| (T@U T@U) Int)
(declare-fun |#Node.at#limited| (T@U T@U Int) Int)
(declare-fun heapFragment (T@U) T@U)
(declare-fun CanAssumeFunctionDefs () Bool)
(declare-fun |##Node.at| (T@U T@U Int) Int)
(declare-fun |#Node.size#limited#trigger| (T@U) Bool)
(declare-fun |#Node.size#limited| (T@U T@U) Int)
(declare-fun |##Node.size| (T@U T@U) Int)
(declare-fun |h0#_0| () T@U)
(declare-fun |m0#_1| () T@U)
(declare-fun |sm0#_2| () T@U)
(declare-fun |h1#_4| () T@U)
(declare-fun |m1#_5| () T@U)
(declare-fun |sm1#_6| () T@U)
(declare-fun TType () T@T)
(declare-fun type@@0 (T@U) T@U)
(declare-fun Mask@@7 () T@U)
(declare-fun SecMask@@7 () T@U)
(declare-fun this@@7 () T@U)
(declare-fun dtype (T@U) T@U)
(declare-fun Heap@@7 () T@U)
(declare-fun %lbl%+2304 () Bool)
(declare-fun |methodK#_9| () Int)
(declare-fun %lbl%@26073 () Bool)
(declare-fun ch () T@U)
(declare-fun %lbl%+25940 () Bool)
(assert (and
(= (Ctor intType) 0)
(= (Ctor boolType) 1)
(forall ((arg0 Int) ) (! (= (U_2_int (int_2_U arg0)) arg0)
 :qid |typeInv:U_2_int|
 :pattern ( (int_2_U arg0))
))
(forall ((x T@U) ) (! (=> (= (type x) intType) (= (int_2_U (U_2_int x)) x))
 :qid |cast:U_2_int|
 :pattern ( (U_2_int x))
))
(forall ((arg0@@0 Int) ) (! (= (type (int_2_U arg0@@0)) intType)
 :qid |funType:int_2_U|
 :pattern ( (int_2_U arg0@@0))
))
(forall ((arg0@@1 Bool) ) (! (iff (U_2_bool (bool_2_U arg0@@1)) arg0@@1)
 :qid |typeInv:U_2_bool|
 :pattern ( (bool_2_U arg0@@1))
))
(forall ((x@@0 T@U) ) (! (=> (= (type x@@0) boolType) (= (bool_2_U (U_2_bool x@@0)) x@@0))
 :qid |cast:U_2_bool|
 :pattern ( (U_2_bool x@@0))
))
(forall ((arg0@@2 Bool) ) (! (= (type (bool_2_U arg0@@2)) boolType)
 :qid |funType:bool_2_U|
 :pattern ( (bool_2_U arg0@@2))
))))
(assert (forall ((x@@1 T@U) ) (! (UOrdering2 x@@1 x@@1)
 :qid |bg:subtype-refl|
 :no-pattern (U_2_int x@@1)
 :no-pattern (U_2_bool x@@1)
)))
(assert (forall ((x@@2 T@U) (y T@U) (z T@U) ) (! (let ((alpha (type x@@2)))
(=> (and
(= (type y) alpha)
(= (type z) alpha)
(UOrdering2 x@@2 y)
(UOrdering2 y z)) (UOrdering2 x@@2 z)))
 :qid |bg:subtype-trans|
 :pattern ( (UOrdering2 x@@2 y) (UOrdering2 y z))
)))
(assert (forall ((x@@3 T@U) (y@@0 T@U) ) (! (let ((alpha@@0 (type x@@3)))
(=> (= (type y@@0) alpha@@0) (=> (and
(UOrdering2 x@@3 y@@0)
(UOrdering2 y@@0 x@@3)) (= x@@3 y@@0))))
 :qid |bg:subtype-antisymm|
 :pattern ( (UOrdering2 x@@3 y@@0) (UOrdering2 y@@0 x@@3))
)))
(assert (and
(= (Ctor PermissionComponentType) 2)
(= (type perm$R) PermissionComponentType)
(= (type perm$N) PermissionComponentType)
(forall ((arg0@@3 T@T) ) (! (= (Ctor (FieldType arg0@@3)) 3)
 :qid |ctor:FieldType|
))
(forall ((arg0@@4 T@T) ) (! (= (FieldTypeInv0 (FieldType arg0@@4)) arg0@@4)
 :qid |typeInv:FieldTypeInv0|
 :pattern ( (FieldType arg0@@4))
))
(= (type joinable) (FieldType intType))
(= (Ctor TypeNameType) 4)
(= (type |token#t|) TypeNameType)
(= (type forkK) (FieldType intType))
(= (Ctor MuType) 5)
(= (type mu) (FieldType MuType))
(= (type held) (FieldType intType))
(= (type rdheld) (FieldType boolType))
(= (type |Node#t|) TypeNameType)
(= (Ctor ModuleNameType) 6)
(= (type |module#default|) ModuleNameType)
(= (Ctor refType) 7)
(= (type Node.next) (FieldType refType))
(= (type Node.value) (FieldType intType))
(= (type Node.valid) (FieldType intType))))
(assert (distinct perm$R perm$N joinable |token#t| forkK mu held rdheld |Node#t| |module#default| Node.next Node.value Node.valid)
)
(assert (> Permission$denominator 0))
(assert (and
(forall ((arg0@@5 T@T) (arg1 T@T) ) (! (= (Ctor (MapType0Type arg0@@5 arg1)) 8)
 :qid |ctor:MapType0Type|
))
(forall ((arg0@@6 T@T) (arg1@@0 T@T) ) (! (= (MapType0TypeInv0 (MapType0Type arg0@@6 arg1@@0)) arg0@@6)
 :qid |typeInv:MapType0TypeInv0|
 :pattern ( (MapType0Type arg0@@6 arg1@@0))
))
(forall ((arg0@@7 T@T) (arg1@@1 T@T) ) (! (= (MapType0TypeInv1 (MapType0Type arg0@@7 arg1@@1)) arg1@@1)
 :qid |typeInv:MapType0TypeInv1|
 :pattern ( (MapType0Type arg0@@7 arg1@@1))
))
(forall ((arg0@@8 T@U) (arg1@@2 T@U) ) (! (let ((aVar1 (MapType0TypeInv1 (type arg0@@8))))
(= (type (MapType0Select arg0@@8 arg1@@2)) aVar1))
 :qid |funType:MapType0Select|
 :pattern ( (MapType0Select arg0@@8 arg1@@2))
))
(forall ((arg0@@9 T@U) (arg1@@3 T@U) (arg2 T@U) ) (! (let ((aVar1@@0 (type arg2)))
(let ((aVar0 (type arg1@@3)))
(= (type (MapType0Store arg0@@9 arg1@@3 arg2)) (MapType0Type aVar0 aVar1@@0))))
 :qid |funType:MapType0Store|
 :pattern ( (MapType0Store arg0@@9 arg1@@3 arg2))
))
(forall ((m T@U) (x0 T@U) (val T@U) ) (! (let ((aVar1@@1 (MapType0TypeInv1 (type m))))
(=> (= (type val) aVar1@@1) (= (MapType0Select (MapType0Store m x0 val) x0) val)))
 :qid |mapAx0:MapType0Select|
 :weight 0
))
(forall ((val@@0 T@U) (m@@0 T@U) (x0@@0 T@U) (y0 T@U) ) (! (or
(= x0@@0 y0)
(= (MapType0Select (MapType0Store m@@0 x0@@0 val@@0) y0) (MapType0Select m@@0 y0)))
 :qid |mapAx1:MapType0Select:0|
 :weight 0
))
(forall ((val@@1 T@U) (m@@1 T@U) (x0@@1 T@U) (y0@@0 T@U) ) (! (or
true
(= (MapType0Select (MapType0Store m@@1 x0@@1 val@@1) y0@@0) (MapType0Select m@@1 y0@@0)))
 :qid |mapAx2:MapType0Select|
 :weight 0
))
(= (type Permission$Zero) (MapType0Type PermissionComponentType intType))))
(assert (= (U_2_int (MapType0Select Permission$Zero perm$R)) 0))
(assert (= (U_2_int (MapType0Select Permission$Zero perm$N)) 0))
(assert (= (type Permission$Full) (MapType0Type PermissionComponentType intType)))
(assert (= (U_2_int (MapType0Select Permission$Full perm$R)) Permission$FullFraction))
(assert (= (U_2_int (MapType0Select Permission$Full perm$N)) 0))
(assert (and
(forall ((arg0@@10 T@T) (arg1@@4 T@T) ) (! (= (Ctor (MapType1Type arg0@@10 arg1@@4)) 9)
 :qid |ctor:MapType1Type|
))
(forall ((arg0@@11 T@T) (arg1@@5 T@T) ) (! (= (MapType1TypeInv0 (MapType1Type arg0@@11 arg1@@5)) arg0@@11)
 :qid |typeInv:MapType1TypeInv0|
 :pattern ( (MapType1Type arg0@@11 arg1@@5))
))
(forall ((arg0@@12 T@T) (arg1@@6 T@T) ) (! (= (MapType1TypeInv1 (MapType1Type arg0@@12 arg1@@6)) arg1@@6)
 :qid |typeInv:MapType1TypeInv1|
 :pattern ( (MapType1Type arg0@@12 arg1@@6))
))
(forall ((arg0@@13 T@U) (arg1@@7 T@U) (arg2@@0 T@U) ) (! (let ((aVar1@@2 (MapType1TypeInv1 (type arg0@@13))))
(= (type (MapType1Select arg0@@13 arg1@@7 arg2@@0)) aVar1@@2))
 :qid |funType:MapType1Select|
 :pattern ( (MapType1Select arg0@@13 arg1@@7 arg2@@0))
))
(forall ((arg0@@14 T@U) (arg1@@8 T@U) (arg2@@1 T@U) (arg3 T@U) ) (! (let ((aVar1@@3 (type arg3)))
(let ((aVar0@@0 (type arg1@@8)))
(= (type (MapType1Store arg0@@14 arg1@@8 arg2@@1 arg3)) (MapType1Type aVar0@@0 aVar1@@3))))
 :qid |funType:MapType1Store|
 :pattern ( (MapType1Store arg0@@14 arg1@@8 arg2@@1 arg3))
))
(forall ((m@@2 T@U) (x0@@2 T@U) (x1 T@U) (val@@2 T@U) ) (! (let ((aVar1@@4 (MapType1TypeInv1 (type m@@2))))
(=> (= (type val@@2) aVar1@@4) (= (MapType1Select (MapType1Store m@@2 x0@@2 x1 val@@2) x0@@2 x1) val@@2)))
 :qid |mapAx0:MapType1Select|
 :weight 0
))
(forall ((val@@3 T@U) (m@@3 T@U) (x0@@3 T@U) (x1@@0 T@U) (y0@@1 T@U) (y1 T@U) ) (! (or
(= x0@@3 y0@@1)
(= (MapType1Select (MapType1Store m@@3 x0@@3 x1@@0 val@@3) y0@@1 y1) (MapType1Select m@@3 y0@@1 y1)))
 :qid |mapAx1:MapType1Select:0|
 :weight 0
))
(forall ((val@@4 T@U) (m@@4 T@U) (x0@@4 T@U) (x1@@1 T@U) (y0@@2 T@U) (y1@@0 T@U) ) (! (or
(= x1@@1 y1@@0)
(= (MapType1Select (MapType1Store m@@4 x0@@4 x1@@1 val@@4) y0@@2 y1@@0) (MapType1Select m@@4 y0@@2 y1@@0)))
 :qid |mapAx1:MapType1Select:1|
 :weight 0
))
(forall ((val@@5 T@U) (m@@5 T@U) (x0@@5 T@U) (x1@@2 T@U) (y0@@3 T@U) (y1@@1 T@U) ) (! (or
true
(= (MapType1Select (MapType1Store m@@5 x0@@5 x1@@2 val@@5) y0@@3 y1@@1) (MapType1Select m@@5 y0@@3 y1@@1)))
 :qid |mapAx2:MapType1Select|
 :weight 0
))
(= (type ZeroMask) (MapType1Type refType (MapType0Type PermissionComponentType intType)))))
(assert (forall ((o T@U) (f T@U) (pc T@U) ) (! (let ((T (FieldTypeInv0 (type f))))
(=> (and
(= (type o) refType)
(= (type f) (FieldType T))
(= (type pc) PermissionComponentType)) (= (U_2_int (MapType0Select (MapType1Select ZeroMask o f) pc)) 0)))
 :qid |crashbpl.26:18|
 :skolemid |0|
 :no-pattern (type o)
 :no-pattern (type f)
 :no-pattern (type pc)
 :no-pattern (U_2_int o)
 :no-pattern (U_2_bool o)
 :no-pattern (U_2_int f)
 :no-pattern (U_2_bool f)
 :no-pattern (U_2_int pc)
 :no-pattern (U_2_bool pc)
)))
(assert (IsGoodMask ZeroMask))
(assert (NonPredicateField joinable))
(assert (NonPredicateField forkK))
(assert (forall ((n Int) ) (! (= (Fractions n) (* n Permission$denominator))
 :qid |crashbpl.37:20|
 :skolemid |1|
 :pattern ( (Fractions n))
)))
(assert (forall ((x@@4 Int) (y@@1 Int) ) (! (=> (and
(<= 0 x@@4)
(<= x@@4 y@@1)) (<= (Fractions x@@4) (Fractions y@@1)))
 :qid |crashbpl.41:15|
 :skolemid |2|
)))
(assert (= Permission$FullFraction (Fractions 100)))
(assert (< 0 channelK))
(assert (< (* 1000 channelK) (Fractions 1)))
(assert (< 0 monitorK))
(assert (< (* 1000 monitorK) (Fractions 1)))
(assert (< 0 predicateK))
(assert (< (* 1000 predicateK) (Fractions 1)))
(assert (= predicateK channelK))
(assert (= channelK monitorK))
(assert (and
(= (Ctor PartialHeapTypeType) 10)
(forall ((arg0@@15 T@U) (arg1@@9 T@U) ) (! (= (type (combine arg0@@15 arg1@@9)) PartialHeapTypeType)
 :qid |funType:combine|
 :pattern ( (combine arg0@@15 arg1@@9))
))))
(assert (forall ((a T@U) (b T@U) ) (! (=> (and
(= (type a) PartialHeapTypeType)
(= (type b) PartialHeapTypeType)) (iff (IsGoodState (combine a b)) (and
(IsGoodState a)
(IsGoodState b))))
 :qid |crashbpl.57:15|
 :skolemid |3|
 :pattern ( (IsGoodState (combine a b)))
)))
(assert (= (type emptyPartialHeap) PartialHeapTypeType))
(assert (IsGoodState emptyPartialHeap))
(assert (NonPredicateField mu))
(assert (forall ((m@@6 T@U) (n@@0 T@U) ) (! (=> (and
(= (type m@@6) MuType)
(= (type n@@0) MuType)) (not (and
(MuBelow m@@6 n@@0)
(MuBelow n@@0 m@@6))))
 :qid |crashbpl.70:15|
 :skolemid |4|
 :pattern ( (MuBelow m@@6 n@@0) (MuBelow n@@0 m@@6))
)))
(assert (forall ((m@@7 T@U) (n@@1 T@U) (o@@0 T@U) ) (! (=> (and
(= (type m@@7) MuType)
(= (type n@@1) MuType)
(= (type o@@0) MuType)
(MuBelow m@@7 n@@1)
(MuBelow n@@1 o@@0)) (MuBelow m@@7 o@@0))
 :qid |crashbpl.73:15|
 :skolemid |5|
 :pattern ( (MuBelow m@@7 n@@1) (MuBelow n@@1 o@@0))
)))
(assert (= (type $LockBottom) MuType))
(assert (forall ((m@@8 T@U) (n@@2 T@U) ) (! (=> (and
(= (type m@@8) MuType)
(= (type n@@2) MuType)
(MuBelow m@@8 n@@2)) (not (= n@@2 $LockBottom)))
 :qid |crashbpl.77:15|
 :skolemid |6|
 :no-pattern (type m@@8)
 :no-pattern (type n@@2)
 :no-pattern (U_2_int m@@8)
 :no-pattern (U_2_bool m@@8)
 :no-pattern (U_2_int n@@2)
 :no-pattern (U_2_bool n@@2)
)))
(assert (NonPredicateField held))
(assert (NonPredicateField rdheld))
(assert (and
(forall ((arg0@@16 T@T) ) (! (= (Ctor (MapType2Type arg0@@16)) 11)
 :qid |ctor:MapType2Type|
))
(forall ((arg0@@17 T@T) ) (! (= (MapType2TypeInv0 (MapType2Type arg0@@17)) arg0@@17)
 :qid |typeInv:MapType2TypeInv0|
 :pattern ( (MapType2Type arg0@@17))
))
(forall ((arg0@@18 T@U) (arg1@@10 T@U) (arg2@@2 T@U) ) (! (let ((a@@0 (FieldTypeInv0 (type arg2@@2))))
(= (type (MapType2Select arg0@@18 arg1@@10 arg2@@2)) a@@0))
 :qid |funType:MapType2Select|
 :pattern ( (MapType2Select arg0@@18 arg1@@10 arg2@@2))
))
(forall ((arg0@@19 T@U) (arg1@@11 T@U) (arg2@@3 T@U) (arg3@@0 T@U) ) (! (let ((aVar0@@1 (type arg1@@11)))
(= (type (MapType2Store arg0@@19 arg1@@11 arg2@@3 arg3@@0)) (MapType2Type aVar0@@1)))
 :qid |funType:MapType2Store|
 :pattern ( (MapType2Store arg0@@19 arg1@@11 arg2@@3 arg3@@0))
))
(forall ((m@@9 T@U) (x0@@6 T@U) (x1@@3 T@U) (val@@6 T@U) ) (! (let ((a@@1 (FieldTypeInv0 (type x1@@3))))
(=> (= (type val@@6) a@@1) (= (MapType2Select (MapType2Store m@@9 x0@@6 x1@@3 val@@6) x0@@6 x1@@3) val@@6)))
 :qid |mapAx0:MapType2Select|
 :weight 0
))
(forall ((val@@7 T@U) (m@@10 T@U) (x0@@7 T@U) (x1@@4 T@U) (y0@@4 T@U) (y1@@2 T@U) ) (! (or
(= x0@@7 y0@@4)
(= (MapType2Select (MapType2Store m@@10 x0@@7 x1@@4 val@@7) y0@@4 y1@@2) (MapType2Select m@@10 y0@@4 y1@@2)))
 :qid |mapAx1:MapType2Select:0|
 :weight 0
))
(forall ((val@@8 T@U) (m@@11 T@U) (x0@@8 T@U) (x1@@5 T@U) (y0@@5 T@U) (y1@@3 T@U) ) (! (or
(= x1@@5 y1@@3)
(= (MapType2Select (MapType2Store m@@11 x0@@8 x1@@5 val@@8) y0@@5 y1@@3) (MapType2Select m@@11 y0@@5 y1@@3)))
 :qid |mapAx1:MapType2Select:1|
 :weight 0
))
(forall ((val@@9 T@U) (m@@12 T@U) (x0@@9 T@U) (x1@@6 T@U) (y0@@6 T@U) (y1@@4 T@U) ) (! (or
true
(= (MapType2Select (MapType2Store m@@12 x0@@9 x1@@6 val@@9) y0@@6 y1@@4) (MapType2Select m@@12 y0@@6 y1@@4)))
 :qid |mapAx2:MapType2Select|
 :weight 0
))))
(assert (forall ((ih T@U) (h T@U) (m@@13 T@U) (sm T@U) ) (! (=> (and
(= (type ih) (MapType2Type refType))
(= (type h) (MapType2Type refType))
(= (type m@@13) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type sm) (MapType1Type refType (MapType0Type PermissionComponentType intType)))) (iff (IsGoodInhaleState ih h m@@13 sm) (and
(forall ((o@@1 T@U) (f@@0 T@U) ) (! (let ((T@@0 (FieldTypeInv0 (type f@@0))))
(=> (and
(= (type o@@1) refType)
(= (type f@@0) (FieldType T@@0))
(CanRead m@@13 sm o@@1 f@@0)) (= (MapType2Select ih o@@1 f@@0) (MapType2Select h o@@1 f@@0))))
 :qid |crashbpl.98:14|
 :skolemid |7|
 :pattern ( (MapType2Select ih o@@1 f@@0))
))
(forall ((o@@2 T@U) ) (! (=> (= (type o@@2) refType) (iff (< 0 (U_2_int (MapType2Select ih o@@2 held))) (< 0 (U_2_int (MapType2Select h o@@2 held)))))
 :qid |crashbpl.99:11|
 :skolemid |8|
 :pattern ( (MapType2Select ih o@@2 held))
))
(forall ((o@@3 T@U) ) (! (=> (= (type o@@3) refType) (iff (U_2_bool (MapType2Select ih o@@3 rdheld)) (U_2_bool (MapType2Select h o@@3 rdheld))))
 :qid |crashbpl.100:11|
 :skolemid |9|
 :pattern ( (MapType2Select ih o@@3 rdheld))
))
(forall ((o@@4 T@U) ) (! (=> (and
(= (type o@@4) refType)
(< 0 (U_2_int (MapType2Select h o@@4 held)))) (= (MapType2Select ih o@@4 mu) (MapType2Select h o@@4 mu)))
 :qid |crashbpl.101:11|
 :skolemid |10|
 :pattern ( (MapType2Select h o@@4 held))
))
(forall ((o@@5 T@U) ) (! (=> (and
(= (type o@@5) refType)
(U_2_bool (MapType2Select h o@@5 rdheld))) (= (MapType2Select ih o@@5 mu) (MapType2Select h o@@5 mu)))
 :qid |crashbpl.102:11|
 :skolemid |11|
 :pattern ( (MapType2Select h o@@5 rdheld))
)))))
 :qid |crashbpl.95:28|
 :skolemid |12|
 :pattern ( (IsGoodInhaleState ih h m@@13 sm))
)))
(assert (forall ((eh T@U) (h@@0 T@U) (m@@14 T@U) (sm@@0 T@U) ) (! (=> (and
(= (type eh) (MapType2Type refType))
(= (type h@@0) (MapType2Type refType))
(= (type m@@14) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type sm@@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))) (iff (IsGoodExhaleState eh h@@0 m@@14 sm@@0) (and
(forall ((o@@6 T@U) (f@@1 T@U) ) (! (let ((T@@1 (FieldTypeInv0 (type f@@1))))
(=> (and
(= (type o@@6) refType)
(= (type f@@1) (FieldType T@@1))
(CanRead m@@14 sm@@0 o@@6 f@@1)) (= (MapType2Select eh o@@6 f@@1) (MapType2Select h@@0 o@@6 f@@1))))
 :qid |crashbpl.107:14|
 :skolemid |13|
 :pattern ( (MapType2Select eh o@@6 f@@1))
))
(forall ((o@@7 T@U) ) (! (=> (= (type o@@7) refType) (iff (< 0 (U_2_int (MapType2Select eh o@@7 held))) (< 0 (U_2_int (MapType2Select h@@0 o@@7 held)))))
 :qid |crashbpl.108:11|
 :skolemid |14|
 :pattern ( (MapType2Select eh o@@7 held))
))
(forall ((o@@8 T@U) ) (! (=> (= (type o@@8) refType) (iff (U_2_bool (MapType2Select eh o@@8 rdheld)) (U_2_bool (MapType2Select h@@0 o@@8 rdheld))))
 :qid |crashbpl.109:11|
 :skolemid |15|
 :pattern ( (MapType2Select eh o@@8 rdheld))
))
(forall ((o@@9 T@U) ) (! (=> (and
(= (type o@@9) refType)
(< 0 (U_2_int (MapType2Select h@@0 o@@9 held)))) (= (MapType2Select eh o@@9 mu) (MapType2Select h@@0 o@@9 mu)))
 :qid |crashbpl.110:11|
 :skolemid |16|
 :pattern ( (MapType2Select h@@0 o@@9 held))
))
(forall ((o@@10 T@U) ) (! (=> (and
(= (type o@@10) refType)
(U_2_bool (MapType2Select h@@0 o@@10 rdheld))) (= (MapType2Select eh o@@10 mu) (MapType2Select h@@0 o@@10 mu)))
 :qid |crashbpl.111:11|
 :skolemid |17|
 :pattern ( (MapType2Select h@@0 o@@10 rdheld))
))
(forall ((o@@11 T@U) ) (! (=> (= (type o@@11) refType) (= (U_2_int (MapType2Select h@@0 o@@11 forkK)) (U_2_int (MapType2Select eh o@@11 forkK))))
 :qid |crashbpl.112:11|
 :skolemid |18|
 :pattern ( (MapType2Select h@@0 o@@11 forkK))
 :pattern ( (MapType2Select eh o@@11 forkK))
))
(forall ((o@@12 T@U) ) (! (=> (= (type o@@12) refType) (= (U_2_int (MapType2Select h@@0 o@@12 held)) (U_2_int (MapType2Select eh o@@12 held))))
 :qid |crashbpl.113:11|
 :skolemid |19|
 :pattern ( (MapType2Select h@@0 o@@12 held))
 :pattern ( (MapType2Select eh o@@12 held))
))
(forall ((o@@13 T@U) (f@@2 T@U) ) (! (=> (and
(= (type o@@13) refType)
(= (type f@@2) (FieldType intType))
(PredicateField f@@2)) (<= (U_2_int (MapType2Select h@@0 o@@13 f@@2)) (U_2_int (MapType2Select eh o@@13 f@@2))))
 :qid |crashbpl.114:11|
 :skolemid |20|
 :pattern ( (MapType2Select eh o@@13 f@@2) (PredicateField f@@2))
)))))
 :qid |crashbpl.104:28|
 :skolemid |21|
 :pattern ( (IsGoodExhaleState eh h@@0 m@@14 sm@@0))
)))
(assert (forall ((m@@15 T@U) (sm@@1 T@U) (obj T@U) (f@@3 T@U) ) (! (let ((T@@2 (FieldTypeInv0 (type f@@3))))
(=> (and
(= (type m@@15) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type sm@@1) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type obj) refType)
(= (type f@@3) (FieldType T@@2))) (iff (CanRead m@@15 sm@@1 obj f@@3) (or
(< 0 (U_2_int (MapType0Select (MapType1Select m@@15 obj f@@3) perm$R)))
(< 0 (U_2_int (MapType0Select (MapType1Select m@@15 obj f@@3) perm$N)))))))
 :qid |crashbpl.121:37|
 :skolemid |22|
 :pattern ( (CanRead m@@15 sm@@1 obj f@@3))
)))
(assert (forall ((m@@16 T@U) (obj@@0 T@U) (f@@4 T@U) ) (! (let ((T@@3 (FieldTypeInv0 (type f@@4))))
(=> (and
(= (type m@@16) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type obj@@0) refType)
(= (type f@@4) (FieldType T@@3))) (iff (CanReadForSure m@@16 obj@@0 f@@4) (or
(< 0 (U_2_int (MapType0Select (MapType1Select m@@16 obj@@0 f@@4) perm$R)))
(< 0 (U_2_int (MapType0Select (MapType1Select m@@16 obj@@0 f@@4) perm$N)))))))
 :qid |crashbpl.125:44|
 :skolemid |23|
 :pattern ( (CanReadForSure m@@16 obj@@0 f@@4))
)))
(assert (forall ((m@@17 T@U) (obj@@1 T@U) (f@@5 T@U) ) (! (let ((T@@4 (FieldTypeInv0 (type f@@5))))
(=> (and
(= (type m@@17) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type obj@@1) refType)
(= (type f@@5) (FieldType T@@4))) (iff (CanWrite m@@17 obj@@1 f@@5) (and
(= (U_2_int (MapType0Select (MapType1Select m@@17 obj@@1 f@@5) perm$R)) Permission$FullFraction)
(= (U_2_int (MapType0Select (MapType1Select m@@17 obj@@1 f@@5) perm$N)) 0)))))
 :qid |crashbpl.129:38|
 :skolemid |24|
 :pattern ( (CanWrite m@@17 obj@@1 f@@5))
)))
(assert (forall ((m@@18 T@U) ) (! (=> (= (type m@@18) (MapType1Type refType (MapType0Type PermissionComponentType intType))) (iff (IsGoodMask m@@18) (forall ((o@@14 T@U) (f@@6 T@U) ) (! (let ((T@@5 (FieldTypeInv0 (type f@@6))))
(=> (and
(= (type o@@14) refType)
(= (type f@@6) (FieldType T@@5))) (and
(<= 0 (U_2_int (MapType0Select (MapType1Select m@@18 o@@14 f@@6) perm$R)))
(=> (NonPredicateField f@@6) (and
(<= (U_2_int (MapType0Select (MapType1Select m@@18 o@@14 f@@6) perm$R)) Permission$FullFraction)
(=> (< 0 (U_2_int (MapType0Select (MapType1Select m@@18 o@@14 f@@6) perm$N))) (< (U_2_int (MapType0Select (MapType1Select m@@18 o@@14 f@@6) perm$R)) Permission$FullFraction))))
(=> (< (U_2_int (MapType0Select (MapType1Select m@@18 o@@14 f@@6) perm$N)) 0) (< 0 (U_2_int (MapType0Select (MapType1Select m@@18 o@@14 f@@6) perm$R)))))))
 :qid |crashbpl.135:14|
 :skolemid |25|
 :no-pattern (type o@@14)
 :no-pattern (type f@@6)
 :no-pattern (U_2_int o@@14)
 :no-pattern (U_2_bool o@@14)
 :no-pattern (U_2_int f@@6)
 :no-pattern (U_2_bool f@@6)
))))
 :qid |crashbpl.133:36|
 :skolemid |26|
 :pattern ( (IsGoodMask m@@18))
)))
(assert (forall ((h@@1 T@U) (m@@19 T@U) (sm@@2 T@U) (o@@15 T@U) (q T@U) ) (! (=> (and
(= (type h@@1) (MapType2Type refType))
(= (type m@@19) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type sm@@2) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type o@@15) refType)
(= (type q) refType)
(wf h@@1 m@@19 sm@@2)
(not (= o@@15 q))
(or
(< 0 (U_2_int (MapType2Select h@@1 o@@15 held)))
(U_2_bool (MapType2Select h@@1 o@@15 rdheld)))
(or
(< 0 (U_2_int (MapType2Select h@@1 q held)))
(U_2_bool (MapType2Select h@@1 q rdheld)))) (not (= (MapType2Select h@@1 o@@15 mu) (MapType2Select h@@1 q mu))))
 :qid |crashbpl.143:15|
 :skolemid |27|
 :pattern ( (wf h@@1 m@@19 sm@@2) (MapType2Select h@@1 o@@15 mu) (MapType2Select h@@1 q mu))
)))
(assert (and
(forall ((arg0@@20 T@U) (arg1@@12 T@U) (arg2@@4 T@U) (arg3@@1 Int) ) (! (= (type (DecPerm arg0@@20 arg1@@12 arg2@@4 arg3@@1)) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
 :qid |funType:DecPerm|
 :pattern ( (DecPerm arg0@@20 arg1@@12 arg2@@4 arg3@@1))
))
(forall ((arg0@@21 Bool) (arg1@@13 T@U) (arg2@@5 T@U) ) (! (let ((T@@6 (type arg1@@13)))
(= (type (q@ite arg0@@21 arg1@@13 arg2@@5)) T@@6))
 :qid |funType:ite|
 :pattern ( (q@ite arg0@@21 arg1@@13 arg2@@5))
))))
(assert (forall ((m@@20 T@U) (o@@16 T@U) (f@@7 T@U) (howMuch Int) (q@@0 T@U) (g T@U) ) (! (let ((U (FieldTypeInv0 (type g))))
(let ((T@@7 (FieldTypeInv0 (type f@@7))))
(=> (and
(= (type m@@20) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type o@@16) refType)
(= (type f@@7) (FieldType T@@7))
(= (type q@@0) refType)
(= (type g) (FieldType U))) (= (U_2_int (MapType0Select (MapType1Select (DecPerm m@@20 o@@16 f@@7 howMuch) q@@0 g) perm$R)) (U_2_int (q@ite (and
(= o@@16 q@@0)
(= f@@7 g)) (int_2_U (- (U_2_int (MapType0Select (MapType1Select m@@20 q@@0 g) perm$R)) howMuch)) (MapType0Select (MapType1Select m@@20 q@@0 g) perm$R)))))))
 :qid |crashbpl.147:20|
 :skolemid |28|
 :pattern ( (MapType0Select (MapType1Select (DecPerm m@@20 o@@16 f@@7 howMuch) q@@0 g) perm$R))
)))
(assert (forall ((arg0@@22 T@U) (arg1@@14 T@U) (arg2@@6 T@U) (arg3@@2 Int) ) (! (= (type (DecEpsilons arg0@@22 arg1@@14 arg2@@6 arg3@@2)) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
 :qid |funType:DecEpsilons|
 :pattern ( (DecEpsilons arg0@@22 arg1@@14 arg2@@6 arg3@@2))
)))
(assert (forall ((m@@21 T@U) (o@@17 T@U) (f@@8 T@U) (howMuch@@0 Int) (q@@1 T@U) (g@@0 T@U) ) (! (let ((U@@0 (FieldTypeInv0 (type g@@0))))
(let ((T@@8 (FieldTypeInv0 (type f@@8))))
(=> (and
(= (type m@@21) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type o@@17) refType)
(= (type f@@8) (FieldType T@@8))
(= (type q@@1) refType)
(= (type g@@0) (FieldType U@@0))) (= (U_2_int (MapType0Select (MapType1Select (DecEpsilons m@@21 o@@17 f@@8 howMuch@@0) q@@1 g@@0) perm$N)) (U_2_int (q@ite (and
(= o@@17 q@@1)
(= f@@8 g@@0)) (int_2_U (- (U_2_int (MapType0Select (MapType1Select m@@21 q@@1 g@@0) perm$N)) howMuch@@0)) (MapType0Select (MapType1Select m@@21 q@@1 g@@0) perm$N)))))))
 :qid |crashbpl.153:20|
 :skolemid |29|
 :pattern ( (MapType0Select (MapType1Select (DecPerm m@@21 o@@17 f@@8 howMuch@@0) q@@1 g@@0) perm$N))
)))
(assert (forall ((arg0@@23 T@U) (arg1@@15 T@U) (arg2@@7 T@U) (arg3@@3 Int) ) (! (= (type (IncPerm arg0@@23 arg1@@15 arg2@@7 arg3@@3)) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
 :qid |funType:IncPerm|
 :pattern ( (IncPerm arg0@@23 arg1@@15 arg2@@7 arg3@@3))
)))
(assert (forall ((m@@22 T@U) (o@@18 T@U) (f@@9 T@U) (howMuch@@1 Int) (q@@2 T@U) (g@@1 T@U) ) (! (let ((U@@1 (FieldTypeInv0 (type g@@1))))
(let ((T@@9 (FieldTypeInv0 (type f@@9))))
(=> (and
(= (type m@@22) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type o@@18) refType)
(= (type f@@9) (FieldType T@@9))
(= (type q@@2) refType)
(= (type g@@1) (FieldType U@@1))) (= (U_2_int (MapType0Select (MapType1Select (IncPerm m@@22 o@@18 f@@9 howMuch@@1) q@@2 g@@1) perm$R)) (U_2_int (q@ite (and
(= o@@18 q@@2)
(= f@@9 g@@1)) (int_2_U (+ (U_2_int (MapType0Select (MapType1Select m@@22 q@@2 g@@1) perm$R)) howMuch@@1)) (MapType0Select (MapType1Select m@@22 q@@2 g@@1) perm$R)))))))
 :qid |crashbpl.159:20|
 :skolemid |30|
 :pattern ( (MapType0Select (MapType1Select (IncPerm m@@22 o@@18 f@@9 howMuch@@1) q@@2 g@@1) perm$R))
)))
(assert (forall ((arg0@@24 T@U) (arg1@@16 T@U) (arg2@@8 T@U) (arg3@@4 Int) ) (! (= (type (IncEpsilons arg0@@24 arg1@@16 arg2@@8 arg3@@4)) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
 :qid |funType:IncEpsilons|
 :pattern ( (IncEpsilons arg0@@24 arg1@@16 arg2@@8 arg3@@4))
)))
(assert (forall ((m@@23 T@U) (o@@19 T@U) (f@@10 T@U) (howMuch@@2 Int) (q@@3 T@U) (g@@2 T@U) ) (! (let ((U@@2 (FieldTypeInv0 (type g@@2))))
(let ((T@@10 (FieldTypeInv0 (type f@@10))))
(=> (and
(= (type m@@23) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type o@@19) refType)
(= (type f@@10) (FieldType T@@10))
(= (type q@@3) refType)
(= (type g@@2) (FieldType U@@2))) (= (U_2_int (MapType0Select (MapType1Select (IncEpsilons m@@23 o@@19 f@@10 howMuch@@2) q@@3 g@@2) perm$N)) (U_2_int (q@ite (and
(= o@@19 q@@3)
(= f@@10 g@@2)) (int_2_U (+ (U_2_int (MapType0Select (MapType1Select m@@23 q@@3 g@@2) perm$N)) howMuch@@2)) (MapType0Select (MapType1Select m@@23 q@@3 g@@2) perm$N)))))))
 :qid |crashbpl.165:20|
 :skolemid |31|
 :pattern ( (MapType0Select (MapType1Select (IncPerm m@@23 o@@19 f@@10 howMuch@@2) q@@3 g@@2) perm$N))
)))
(assert (forall ((arg0@@25 T@U) (arg1@@17 T@U) (arg2@@9 T@U) (arg3@@5 T@U) ) (! (= (type (Havocing arg0@@25 arg1@@17 arg2@@9 arg3@@5)) (MapType2Type refType))
 :qid |funType:Havocing|
 :pattern ( (Havocing arg0@@25 arg1@@17 arg2@@9 arg3@@5))
)))
(assert (forall ((h@@2 T@U) (o@@20 T@U) (f@@11 T@U) (newValue T@U) (q@@4 T@U) (g@@3 T@U) ) (! (let ((U@@3 (type newValue)))
(let ((T@@11 (FieldTypeInv0 (type f@@11))))
(=> (and
(= (type h@@2) (MapType2Type refType))
(= (type o@@20) refType)
(= (type f@@11) (FieldType T@@11))
(= (type q@@4) refType)
(= (type g@@3) (FieldType U@@3))) (= (MapType2Select (Havocing h@@2 o@@20 f@@11 newValue) q@@4 g@@3) (q@ite (and
(= o@@20 q@@4)
(= f@@11 g@@3)) newValue (MapType2Select h@@2 q@@4 g@@3))))))
 :qid |crashbpl.171:20|
 :skolemid |32|
 :pattern ( (MapType2Select (Havocing h@@2 o@@20 f@@11 newValue) q@@4 g@@3))
)))
(assert (forall ((m@@24 T@U) ) (! (=> (= (type m@@24) (MapType1Type refType (MapType0Type PermissionComponentType intType))) (iff (EmptyMask m@@24) (forall ((o@@21 T@U) (f@@12 T@U) ) (! (let ((T@@12 (FieldTypeInv0 (type f@@12))))
(=> (and
(= (type o@@21) refType)
(= (type f@@12) (FieldType T@@12))
(NonPredicateField f@@12)) (and
(<= (U_2_int (MapType0Select (MapType1Select m@@24 o@@21 f@@12) perm$R)) 0)
(<= (U_2_int (MapType0Select (MapType1Select m@@24 o@@21 f@@12) perm$N)) 0))))
 :qid |crashbpl.183:74|
 :skolemid |33|
 :no-pattern (type o@@21)
 :no-pattern (type f@@12)
 :no-pattern (U_2_int o@@21)
 :no-pattern (U_2_bool o@@21)
 :no-pattern (U_2_int f@@12)
 :no-pattern (U_2_bool f@@12)
))))
 :qid |crashbpl.183:15|
 :skolemid |34|
 :pattern ( (EmptyMask m@@24))
)))
(assert (= (type ZeroCredits) (MapType0Type refType intType)))
(assert (forall ((o@@22 T@U) ) (! (=> (= (type o@@22) refType) (= (U_2_int (MapType0Select ZeroCredits o@@22)) 0))
 :qid |crashbpl.186:15|
 :skolemid |35|
 :no-pattern (type o@@22)
 :no-pattern (U_2_int o@@22)
 :no-pattern (U_2_bool o@@22)
)))
(assert (= (type null) refType))
(assert (forall ((c T@U) ) (! (=> (= (type c) (MapType0Type refType intType)) (iff (EmptyCredits c) (forall ((o@@23 T@U) ) (! (=> (and
(= (type o@@23) refType)
(not (= o@@23 null))) (= (U_2_int (MapType0Select c o@@23)) 0))
 :qid |crashbpl.188:80|
 :skolemid |36|
 :no-pattern (type o@@23)
 :no-pattern (U_2_int o@@23)
 :no-pattern (U_2_bool o@@23)
))))
 :qid |crashbpl.188:15|
 :skolemid |37|
 :pattern ( (EmptyCredits c))
)))
(assert (forall ((f@@13 T@U) ) (! (let ((T@@13 (FieldTypeInv0 (type f@@13))))
(=> (and
(= (type f@@13) (FieldType T@@13))
(NonPredicateField f@@13)) (not (PredicateField f@@13))))
 :qid |crashbpl.192:18|
 :skolemid |38|
 :no-pattern (type f@@13)
 :no-pattern (U_2_int f@@13)
 :no-pattern (U_2_bool f@@13)
)))
(assert (forall ((f@@14 T@U) ) (! (let ((T@@14 (FieldTypeInv0 (type f@@14))))
(=> (and
(= (type f@@14) (FieldType T@@14))
(PredicateField f@@14)) (not (NonPredicateField f@@14))))
 :qid |crashbpl.193:18|
 :skolemid |39|
 :no-pattern (type f@@14)
 :no-pattern (U_2_int f@@14)
 :no-pattern (U_2_bool f@@14)
)))
(assert (forall ((m1 T@U) (m2 T@U) ) (! (=> (and
(= (type m1) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type m2) (MapType1Type refType (MapType0Type PermissionComponentType intType)))) (iff (submask m1 m2) (forall ((o@@24 T@U) (f@@15 T@U) ) (! (let ((T@@15 (FieldTypeInv0 (type f@@15))))
(=> (and
(= (type o@@24) refType)
(= (type f@@15) (FieldType T@@15))) (or
(< (U_2_int (MapType0Select (MapType1Select m1 o@@24 f@@15) perm$R)) (U_2_int (MapType0Select (MapType1Select m2 o@@24 f@@15) perm$R)))
(and
(= (U_2_int (MapType0Select (MapType1Select m1 o@@24 f@@15) perm$R)) (U_2_int (MapType0Select (MapType1Select m2 o@@24 f@@15) perm$R)))
(<= (U_2_int (MapType0Select (MapType1Select m1 o@@24 f@@15) perm$N)) (U_2_int (MapType0Select (MapType1Select m2 o@@24 f@@15) perm$N)))))))
 :qid |crashbpl.198:35|
 :skolemid |40|
 :no-pattern (type o@@24)
 :no-pattern (type f@@15)
 :no-pattern (U_2_int o@@24)
 :no-pattern (U_2_bool o@@24)
 :no-pattern (U_2_int f@@15)
 :no-pattern (U_2_bool f@@15)
))))
 :qid |crashbpl.197:15|
 :skolemid |41|
 :pattern ( (submask m1 m2))
)))
(assert (forall ((con Bool) (a@@2 T@U) (b@@0 T@U) ) (! (let ((T@@16 (type a@@2)))
(=> (and
(= (type b@@0) T@@16)
con) (= (q@ite con a@@2 b@@0) a@@2)))
 :qid |crashbpl.206:18|
 :skolemid |42|
 :pattern ( (q@ite con a@@2 b@@0))
)))
(assert (forall ((con@@0 Bool) (a@@3 T@U) (b@@1 T@U) ) (! (let ((T@@17 (type a@@3)))
(=> (and
(= (type b@@1) T@@17)
(not con@@0)) (= (q@ite con@@0 a@@3 b@@1) b@@1)))
 :qid |crashbpl.207:18|
 :skolemid |43|
 :pattern ( (q@ite con@@0 a@@3 b@@1))
)))
(assert (forall ((x@@5 Int) (y@@2 Int) ) (! (= (int_mod x@@5 y@@2) (- x@@5 (* (int_div x@@5 y@@2) y@@2)))
 :qid |crashbpl.214:15|
 :skolemid |44|
 :pattern ( (int_mod x@@5 y@@2))
 :pattern ( (int_div x@@5 y@@2))
)))
(assert (forall ((x@@6 Int) (y@@3 Int) ) (! (=> (< 0 y@@3) (and
(<= 0 (int_mod x@@6 y@@3))
(< (int_mod x@@6 y@@3) y@@3)))
 :qid |crashbpl.217:15|
 :skolemid |45|
 :pattern ( (int_mod x@@6 y@@3))
)))
(assert (forall ((x@@7 Int) (y@@4 Int) ) (! (=> (< y@@4 0) (and
(< y@@4 (int_mod x@@7 y@@4))
(<= (int_mod x@@7 y@@4) 0)))
 :qid |crashbpl.218:15|
 :skolemid |46|
 :pattern ( (int_mod x@@7 y@@4))
)))
(assert (forall ((a@@4 Int) (b@@2 Int) (d Int) ) (! (=> (and
(<= 2 d)
(= (int_mod a@@4 d) (int_mod b@@2 d))
(< a@@4 b@@2)) (<= (+ a@@4 d) b@@2))
 :qid |crashbpl.222:15|
 :skolemid |47|
 :pattern ( (int_mod a@@4 d) (int_mod b@@2 d))
)))
(assert (NonPredicateField Node.next))
(assert (NonPredicateField Node.value))
(assert (= (type CurrentModule) ModuleNameType))
(assert (forall ((Mask T@U) (SecMask T@U) (Heap T@U) (this T@U) (|i#8| Int) ) (! (=> (and
(= (type Mask) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type SecMask) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Heap) (MapType2Type refType))
(= (type this) refType)) (=> (and
(wf Heap Mask SecMask)
(= CurrentModule |module#default|)
true
(CanRead Mask SecMask this Node.valid)
(<= 0 |i#8|)
(< |i#8| (|#Node.size| Heap this))) (= (|#Node.at| Heap this |i#8|) (U_2_int (q@ite (= |i#8| 0) (MapType2Select Heap this Node.value) (int_2_U (|#Node.at#limited| Heap (MapType2Select Heap this Node.next) (- |i#8| 1))))))))
 :qid |crashbpl.1355:15|
 :skolemid |57|
 :pattern ( (|#Node.at#limited#trigger| this |i#8|) (wf Heap Mask SecMask) (|#Node.valid#trigger| this))
 :pattern ( (|#Node.at| Heap this |i#8|) (wf Heap Mask SecMask))
)))
(assert (forall ((Mask@@0 T@U) (SecMask@@0 T@U) (Heap@@0 T@U) (this@@0 T@U) (|i#8@@0| Int) ) (! (=> (and
(= (type Mask@@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type SecMask@@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Heap@@0) (MapType2Type refType))
(= (type this@@0) refType)
(wf Heap@@0 Mask@@0 SecMask@@0)) (= (|#Node.at| Heap@@0 this@@0 |i#8@@0|) (|#Node.at#limited| Heap@@0 this@@0 |i#8@@0|)))
 :qid |crashbpl.1357:15|
 :skolemid |58|
 :pattern ( (|#Node.at| Heap@@0 this@@0 |i#8@@0|) (wf Heap@@0 Mask@@0 SecMask@@0))
 :pattern ( (|#Node.at#limited| Heap@@0 this@@0 |i#8@@0|) (wf Heap@@0 Mask@@0 SecMask@@0) (|#Node.valid#trigger| this@@0))
)))
(assert (forall ((Mask@@1 T@U) (SecMask@@1 T@U) (Heap@@1 T@U) (this@@1 T@U) (|i#8@@1| Int) ) (! (=> (and
(= (type Mask@@1) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type SecMask@@1) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Heap@@1) (MapType2Type refType))
(= (type this@@1) refType)
(wf Heap@@1 Mask@@1 SecMask@@1)) (|#Node.at#limited#trigger| this@@1 |i#8@@1|))
 :qid |crashbpl.1359:15|
 :skolemid |59|
 :pattern ( (|#Node.at#limited| Heap@@1 this@@1 |i#8@@1|) (wf Heap@@1 Mask@@1 SecMask@@1))
)))
(assert (forall ((arg0@@26 T@U) ) (! (= (type (heapFragment arg0@@26)) PartialHeapTypeType)
 :qid |funType:heapFragment|
 :pattern ( (heapFragment arg0@@26))
)))
(assert (forall ((Heap@@2 T@U) (Mask@@2 T@U) (SecMask@@2 T@U) (this@@2 T@U) (|i#8@@2| Int) ) (! (=> (and
(= (type Heap@@2) (MapType2Type refType))
(= (type Mask@@2) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type SecMask@@2) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type this@@2) refType)
(wf Heap@@2 Mask@@2 SecMask@@2)
(IsGoodState (heapFragment (MapType2Select Heap@@2 this@@2 Node.valid)))
CanAssumeFunctionDefs) (= (|#Node.at#limited| Heap@@2 this@@2 |i#8@@2|) (|##Node.at| (heapFragment (MapType2Select Heap@@2 this@@2 Node.valid)) this@@2 |i#8@@2|)))
 :qid |crashbpl.1361:15|
 :skolemid |60|
 :pattern ( (|#Node.at#limited| Heap@@2 this@@2 |i#8@@2|) (wf Heap@@2 Mask@@2 SecMask@@2))
)))
(assert (forall ((Mask@@3 T@U) (SecMask@@3 T@U) (Heap@@3 T@U) (this@@3 T@U) ) (! (=> (and
(= (type Mask@@3) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type SecMask@@3) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Heap@@3) (MapType2Type refType))
(= (type this@@3) refType)
(wf Heap@@3 Mask@@3 SecMask@@3)
(= CurrentModule |module#default|)
true
(CanRead Mask@@3 SecMask@@3 this@@3 Node.valid)) (= (|#Node.size| Heap@@3 this@@3) (U_2_int (q@ite (not (= (MapType2Select Heap@@3 this@@3 Node.next) null)) (int_2_U (+ 1 (|#Node.size#limited| Heap@@3 (MapType2Select Heap@@3 this@@3 Node.next)))) (int_2_U 1)))))
 :qid |crashbpl.1546:15|
 :skolemid |61|
 :pattern ( (|#Node.size#limited#trigger| this@@3) (wf Heap@@3 Mask@@3 SecMask@@3) (|#Node.valid#trigger| this@@3))
 :pattern ( (|#Node.size| Heap@@3 this@@3) (wf Heap@@3 Mask@@3 SecMask@@3))
)))
(assert (forall ((Mask@@4 T@U) (SecMask@@4 T@U) (Heap@@4 T@U) (this@@4 T@U) ) (! (=> (and
(= (type Mask@@4) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type SecMask@@4) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Heap@@4) (MapType2Type refType))
(= (type this@@4) refType)
(wf Heap@@4 Mask@@4 SecMask@@4)) (= (|#Node.size| Heap@@4 this@@4) (|#Node.size#limited| Heap@@4 this@@4)))
 :qid |crashbpl.1548:15|
 :skolemid |62|
 :pattern ( (|#Node.size| Heap@@4 this@@4) (wf Heap@@4 Mask@@4 SecMask@@4))
 :pattern ( (|#Node.size#limited| Heap@@4 this@@4) (wf Heap@@4 Mask@@4 SecMask@@4) (|#Node.valid#trigger| this@@4))
)))
(assert (forall ((Mask@@5 T@U) (SecMask@@5 T@U) (Heap@@5 T@U) (this@@5 T@U) ) (! (=> (and
(= (type Mask@@5) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type SecMask@@5) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Heap@@5) (MapType2Type refType))
(= (type this@@5) refType)
(wf Heap@@5 Mask@@5 SecMask@@5)) (|#Node.size#limited#trigger| this@@5))
 :qid |crashbpl.1550:15|
 :skolemid |63|
 :pattern ( (|#Node.size#limited| Heap@@5 this@@5) (wf Heap@@5 Mask@@5 SecMask@@5))
)))
(assert (forall ((Heap@@6 T@U) (Mask@@6 T@U) (SecMask@@6 T@U) (this@@6 T@U) ) (! (=> (and
(= (type Heap@@6) (MapType2Type refType))
(= (type Mask@@6) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type SecMask@@6) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type this@@6) refType)
(wf Heap@@6 Mask@@6 SecMask@@6)
(IsGoodState (heapFragment (MapType2Select Heap@@6 this@@6 Node.valid)))
CanAssumeFunctionDefs) (= (|#Node.size#limited| Heap@@6 this@@6) (|##Node.size| (heapFragment (MapType2Select Heap@@6 this@@6 Node.valid)) this@@6)))
 :qid |crashbpl.1552:15|
 :skolemid |64|
 :pattern ( (|#Node.size#limited| Heap@@6 this@@6) (wf Heap@@6 Mask@@6 SecMask@@6))
)))
(assert (PredicateField Node.valid))
(assert (and
(= (type |h0#_0|) (MapType2Type refType))
(= (type |m0#_1|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |sm0#_2|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |h1#_4|) (MapType2Type refType))
(= (type |m1#_5|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |sm1#_6|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (Ctor TType) 12)
(forall ((arg0@@27 T@U) ) (! (= (type (type@@0 arg0@@27)) TType)
 :qid |funType:type|
 :pattern ( (type@@0 arg0@@27))
))
(= (type Mask@@7) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type SecMask@@7) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type this@@7) refType)
(forall ((arg0@@28 T@U) ) (! (= (type (dtype arg0@@28)) TypeNameType)
 :qid |funType:dtype|
 :pattern ( (dtype arg0@@28))
))
(= (type Heap@@7) (MapType2Type refType))))
(push 1)
(set-info :boogie-vc-id Node$monitorinvariant$checkDefinedness)
(assert (not
(let ((anon0_correct (=> (! (and %lbl%+2304 true) :lblpos +2304) (=> (and
(< 0 |methodK#_9|)
(< (* 1000 |methodK#_9|) (Fractions 1))
(wf |h0#_0| |m0#_1| |sm0#_2|)
(wf |h1#_4| |m1#_5| |sm1#_6|)) (and
(! (or %lbl%@26073 (forall ((ch@@0 T@U) ) (! (=> (= (type ch@@0) refType) (or
(= ch@@0 null)
(<= 0 (U_2_int (MapType0Select ZeroCredits ch@@0)))))
 :qid |crashbpl.262:84|
 :skolemid |48|
 :no-pattern (type ch@@0)
 :no-pattern (U_2_int ch@@0)
 :no-pattern (U_2_bool ch@@0)
))) :lblneg @26073)
(=> (forall ((ch@@1 T@U) ) (! (=> (= (type ch@@1) refType) (or
(= ch@@1 null)
(<= 0 (U_2_int (MapType0Select ZeroCredits ch@@1)))))
 :qid |crashbpl.262:84|
 :skolemid |48|
 :no-pattern (type@@0 ch)
 :no-pattern (type ch@@1)
 :no-pattern (U_2_int ch@@1)
 :no-pattern (U_2_bool ch@@1)
)) true))))))
(let ((PreconditionGeneratedEntry_correct (=> (! (and %lbl%+25940 true) :lblpos +25940) (=> (IsGoodMask Mask@@7) (=> (and
(IsGoodMask SecMask@@7)
(or
(= this@@7 null)
(= (dtype this@@7) |Node#t|))
(not (= this@@7 null))
(wf Heap@@7 Mask@@7 SecMask@@7)) anon0_correct)))))
PreconditionGeneratedEntry_correct))
))
(check-sat)
(pop 1)
(declare-fun |exhaleMask#_17@0| () T@U)
(declare-fun this@@8 () T@U)
(declare-fun Heap@0 () T@U)
(declare-fun |exhaleHeap#_16@0| () T@U)
(declare-fun Mask@0 () T@U)
(declare-fun Mask@1 () T@U)
(declare-fun Credits () T@U)
(declare-fun Mask@2 () T@U)
(declare-fun %lbl%+2854 () Bool)
(declare-fun %lbl%+2852 () Bool)
(declare-fun %lbl%+2850 () Bool)
(declare-fun %lbl%+2848 () Bool)
(declare-fun |methodK#_10| () Int)
(declare-fun %lbl%@27703 () Bool)
(declare-fun %lbl%@27794 () Bool)
(declare-fun |funcappK#_15| () Int)
(declare-fun %lbl%@27844 () Bool)
(declare-fun %lbl%@27852 () Bool)
(declare-fun %lbl%+27334 () Bool)
(assert (and
(= (type |exhaleMask#_17@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type this@@8) refType)
(= (type Heap@0) (MapType2Type refType))
(= (type |exhaleHeap#_16@0|) (MapType2Type refType))
(= (type Mask@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@1) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Credits) (MapType0Type refType intType))
(= (type Mask@2) (MapType1Type refType (MapType0Type PermissionComponentType intType)))))
(push 1)
(set-info :boogie-vc-id Node.init$checkDefinedness)
(assert (not
(let ((anon2_correct (=> (! (and %lbl%+2854 true) :lblpos +2854) true)))
(let ((anon3_Else_correct (=> (! (and %lbl%+2852 true) :lblpos +2852) (=> (CanRead |exhaleMask#_17@0| ZeroMask this@@8 Node.valid) anon2_correct))))
(let ((anon3_Then_correct (=> (! (and %lbl%+2850 true) :lblpos +2850) (=> (and
(not (CanRead |exhaleMask#_17@0| ZeroMask this@@8 Node.valid))
(< (U_2_int (MapType2Select Heap@0 this@@8 Node.valid)) (U_2_int (MapType2Select |exhaleHeap#_16@0| this@@8 Node.valid)))) anon2_correct))))
(let ((anon0_correct@@0 (=> (! (and %lbl%+2848 true) :lblpos +2848) (=> (and
(< 0 |methodK#_10|)
(< (* 1000 |methodK#_10|) (Fractions 1))) (=> (and
CanAssumeFunctionDefs
(not (= this@@8 null))
(wf Heap@@7 ZeroMask ZeroMask)
(or
(= (MapType2Select Heap@@7 this@@8 Node.next) null)
(= (dtype (MapType2Select Heap@@7 this@@8 Node.next)) |Node#t|))
(> (Fractions 100) 0)
(= Mask@0 (MapType1Store ZeroMask this@@8 Node.next (MapType0Store (MapType1Select ZeroMask this@@8 Node.next) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select ZeroMask this@@8 Node.next) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@0)
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@8 Node.next)))) (=> (and
(wf Heap@@7 Mask@0 ZeroMask)
(wf Heap@@7 Mask@0 ZeroMask)
(not (= this@@8 null))
(wf Heap@@7 Mask@0 ZeroMask)
(> (Fractions 100) 0)
(= Mask@1 (MapType1Store Mask@0 this@@8 Node.value (MapType0Store (MapType1Select Mask@0 this@@8 Node.value) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@0 this@@8 Node.value) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@1)
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@8 Node.value)))
(wf Heap@@7 Mask@1 ZeroMask)
(wf Heap@@7 Mask@1 ZeroMask)
(IsGoodMask Mask@1)
(wf Heap@@7 Mask@1 ZeroMask)
(= Heap@@7 Heap@@7)
(= Mask@1 Mask@@7)
(= ZeroMask SecMask@@7)
(= ZeroCredits Credits)) (and
(! (or %lbl%@27703 (not (= this@@8 null))) :lblneg @27703)
(=> (not (= this@@8 null)) (=> (and
(not (= this@@8 null))
(wf Heap@0 ZeroMask ZeroMask)
(> (Fractions 100) 0)
(= Mask@2 (MapType1Store ZeroMask this@@8 Node.valid (MapType0Store (MapType1Select ZeroMask this@@8 Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select ZeroMask this@@8 Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@2)
(IsGoodState (heapFragment (MapType2Select Heap@0 this@@8 Node.valid)))
(wf Heap@0 Mask@2 ZeroMask)
(wf Heap@0 Mask@2 ZeroMask)) (and
(! (or %lbl%@27794 (=> true (not (= this@@8 null)))) :lblneg @27794)
(=> (=> true (not (= this@@8 null))) (=> (and
(< 0 |funcappK#_15|)
(< (* 1000 |funcappK#_15|) (Fractions 1))
(wf Heap@0 Mask@2 ZeroMask)) (and
(! (or %lbl%@27844 (> (Fractions 100) 0)) :lblneg @27844)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@27852 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@2 this@@8 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@2 this@@8 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@2 this@@8 Node.valid) perm$N)))))) :lblneg @27852)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@2 this@@8 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@2 this@@8 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@2 this@@8 Node.valid) perm$N))))) (=> (= |exhaleMask#_17@0| (MapType1Store Mask@2 this@@8 Node.valid (MapType0Store (MapType1Select Mask@2 this@@8 Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@2 this@@8 Node.valid) perm$R)) (Fractions 100)))))) (and
anon3_Then_correct
anon3_Else_correct))))))))))))))))))
(let ((PreconditionGeneratedEntry_correct@@0 (=> (! (and %lbl%+27334 true) :lblpos +27334) (=> (IsGoodMask Mask@@7) (=> (and
(IsGoodMask SecMask@@7)
(or
(= this@@8 null)
(= (dtype this@@8) |Node#t|))
(not (= this@@8 null))
(wf Heap@@7 Mask@@7 SecMask@@7)) anon0_correct@@0)))))
PreconditionGeneratedEntry_correct@@0)))))
))
(check-sat)
(pop 1)
(declare-fun |exhaleMask#_29@0| () T@U)
(declare-fun |exhaleHeap#_28@4| () T@U)
(declare-fun Heap@1 () T@U)
(declare-fun this@@9 () T@U)
(declare-fun |exhaleHeap#_28@3| () T@U)
(declare-fun |exhaleHeap#_28@2| () T@U)
(declare-fun |exhaleHeap#_28@1| () T@U)
(declare-fun |exhaleHeap#_28@0| () T@U)
(declare-fun Mask@6 () T@U)
(declare-fun Mask@5 () T@U)
(declare-fun Mask@3 () T@U)
(declare-fun Mask@4 () T@U)
(declare-fun Mask@0@@0 () T@U)
(declare-fun Mask@1@@0 () T@U)
(declare-fun Heap@0@@0 () T@U)
(declare-fun Mask@2@@0 () T@U)
(declare-fun %lbl%+3782 () Bool)
(declare-fun %lbl%@29452 () Bool)
(declare-fun %lbl%@29518 () Bool)
(declare-fun ch@@2 () T@U)
(declare-fun %lbl%+3780 () Bool)
(declare-fun %lbl%+3778 () Bool)
(declare-fun %lbl%+3776 () Bool)
(declare-fun %lbl%+3774 () Bool)
(declare-fun %lbl%+3770 () Bool)
(declare-fun %lbl%+3765 () Bool)
(declare-fun %lbl%+3763 () Bool)
(declare-fun %lbl%+3761 () Bool)
(declare-fun |predVer#_20@0| () Int)
(declare-fun %lbl%@29159 () Bool)
(declare-fun %lbl%@29168 () Bool)
(declare-fun %lbl%@29176 () Bool)
(declare-fun %lbl%+3757 () Bool)
(declare-fun %lbl%+3755 () Bool)
(declare-fun %lbl%@28882 () Bool)
(declare-fun %lbl%@28890 () Bool)
(declare-fun %lbl%+3753 () Bool)
(declare-fun |methodK#_10@@0| () Int)
(declare-fun %lbl%@28543 () Bool)
(declare-fun %lbl%@28572 () Bool)
(declare-fun |v#0| () Int)
(declare-fun |foldK#_22| () Int)
(declare-fun %lbl%@28636 () Bool)
(declare-fun %lbl%@28642 () Bool)
(declare-fun %lbl%@28650 () Bool)
(declare-fun %lbl%@28750 () Bool)
(declare-fun %lbl%@28758 () Bool)
(declare-fun %lbl%+28164 () Bool)
(assert (and
(= (type |exhaleMask#_29@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |exhaleHeap#_28@4|) (MapType2Type refType))
(= (type Heap@1) (MapType2Type refType))
(= (type this@@9) refType)
(= (type |exhaleHeap#_28@3|) (MapType2Type refType))
(= (type |exhaleHeap#_28@2|) (MapType2Type refType))
(= (type |exhaleHeap#_28@1|) (MapType2Type refType))
(= (type |exhaleHeap#_28@0|) (MapType2Type refType))
(= (type Mask@6) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@5) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@3) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@4) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@0@@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@1@@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Heap@0@@0) (MapType2Type refType))
(= (type Mask@2@@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))))
(push 1)
(set-info :boogie-vc-id Node.init)
(assert (not
(let ((anon7_correct (=> (! (and %lbl%+3782 true) :lblpos +3782) (=> (and
(IsGoodMask |exhaleMask#_29@0|)
(wf |exhaleHeap#_28@4| |exhaleMask#_29@0| ZeroMask)) (and
(! (or %lbl%@29452 (forall ((|lk#_31| T@U) ) (! (=> (= (type |lk#_31|) refType) (or
(and
(iff (< 0 (U_2_int (MapType2Select |exhaleHeap#_28@4| |lk#_31| held))) (< 0 (U_2_int (MapType2Select Heap@@7 |lk#_31| held))))
(iff (U_2_bool (MapType2Select |exhaleHeap#_28@4| |lk#_31| rdheld)) (U_2_bool (MapType2Select Heap@@7 |lk#_31| rdheld))))
false))
 :qid |crashbpl.476:78|
 :skolemid |49|
 :pattern ( (MapType2Select |exhaleHeap#_28@4| |lk#_31| held))
 :pattern ( (MapType2Select |exhaleHeap#_28@4| |lk#_31| rdheld))
))) :lblneg @29452)
(=> (forall ((|lk#_31@@0| T@U) ) (! (=> (= (type |lk#_31@@0|) refType) (or
(and
(iff (< 0 (U_2_int (MapType2Select |exhaleHeap#_28@4| |lk#_31@@0| held))) (< 0 (U_2_int (MapType2Select Heap@@7 |lk#_31@@0| held))))
(iff (U_2_bool (MapType2Select |exhaleHeap#_28@4| |lk#_31@@0| rdheld)) (U_2_bool (MapType2Select Heap@@7 |lk#_31@@0| rdheld))))
false))
 :qid |crashbpl.476:78|
 :skolemid |49|
 :pattern ( (MapType2Select |exhaleHeap#_28@4| |lk#_31@@0| held))
 :pattern ( (MapType2Select |exhaleHeap#_28@4| |lk#_31@@0| rdheld))
)) (and
(! (or %lbl%@29518 (forall ((ch@@3 T@U) ) (! (=> (= (type ch@@3) refType) (or
(= ch@@3 null)
(<= 0 (U_2_int (MapType0Select ZeroCredits ch@@3)))))
 :qid |crashbpl.477:80|
 :skolemid |50|
 :no-pattern (type ch@@3)
 :no-pattern (U_2_int ch@@3)
 :no-pattern (U_2_bool ch@@3)
))) :lblneg @29518)
(=> (forall ((ch@@4 T@U) ) (! (=> (= (type ch@@4) refType) (or
(= ch@@4 null)
(<= 0 (U_2_int (MapType0Select ZeroCredits ch@@4)))))
 :qid |crashbpl.477:80|
 :skolemid |50|
 :no-pattern (type@@0 ch@@2)
 :no-pattern (type ch@@4)
 :no-pattern (U_2_int ch@@4)
 :no-pattern (U_2_bool ch@@4)
)) true))))))))
(let ((anon10_Else_correct (=> (! (and %lbl%+3780 true) :lblpos +3780) (=> (and
(not (CanRead |exhaleMask#_29@0| ZeroMask this@@9 Node.valid))
(= |exhaleHeap#_28@4| |exhaleHeap#_28@0|)) anon7_correct))))
(let ((anon11_Else_correct (=> (! (and %lbl%+3778 true) :lblpos +3778) (=> (and
(= (MapType2Select Heap@1 this@@9 Node.next) null)
(= |exhaleHeap#_28@4| |exhaleHeap#_28@2|)) anon7_correct))))
(let ((anon11_Then_correct (=> (! (and %lbl%+3776 true) :lblpos +3776) (=> (not (= (MapType2Select Heap@1 this@@9 Node.next) null)) (=> (and
(= |exhaleHeap#_28@3| (MapType2Store |exhaleHeap#_28@2| (MapType2Select Heap@1 this@@9 Node.next) Node.valid (MapType2Select Heap@1 (MapType2Select Heap@1 this@@9 Node.next) Node.valid)))
(= |exhaleHeap#_28@4| |exhaleHeap#_28@3|)) anon7_correct)))))
(let ((anon10_Then_correct (=> (! (and %lbl%+3774 true) :lblpos +3774) (=> (CanRead |exhaleMask#_29@0| ZeroMask this@@9 Node.valid) (=> (and
(= |exhaleHeap#_28@1| (MapType2Store |exhaleHeap#_28@0| this@@9 Node.next (MapType2Select Heap@1 this@@9 Node.next)))
(= |exhaleHeap#_28@2| (MapType2Store |exhaleHeap#_28@1| this@@9 Node.value (MapType2Select Heap@1 this@@9 Node.value)))) (and
anon11_Then_correct
anon11_Else_correct))))))
(let ((anon4_correct (=> (! (and %lbl%+3770 true) :lblpos +3770) (=> (wf Heap@1 |exhaleMask#_29@0| ZeroMask) (=> (and
(wf Heap@1 Mask@6 ZeroMask)
(IsGoodExhaleState |exhaleHeap#_28@0| Heap@1 |exhaleMask#_29@0| ZeroMask)) (and
anon10_Then_correct
anon10_Else_correct))))))
(let ((anon9_Else_correct (=> (! (and %lbl%+3765 true) :lblpos +3765) (=> (CanRead |exhaleMask#_29@0| ZeroMask this@@9 Node.valid) anon4_correct))))
(let ((anon9_Then_correct (=> (! (and %lbl%+3763 true) :lblpos +3763) (=> (and
(not (CanRead |exhaleMask#_29@0| ZeroMask this@@9 Node.valid))
(< (U_2_int (MapType2Select Heap@1 this@@9 Node.valid)) (U_2_int (MapType2Select |exhaleHeap#_28@0| this@@9 Node.valid)))) anon4_correct))))
(let ((anon2_correct@@0 (=> (! (and %lbl%+3761 true) :lblpos +3761) (=> (and
(IsGoodMask Mask@5)
(wf Heap@1 Mask@5 ZeroMask)) (=> (and
(not (= this@@9 null))
(wf Heap@1 Mask@5 ZeroMask)
(> (Fractions 100) 0)
(= Mask@6 (MapType1Store Mask@5 this@@9 Node.valid (MapType0Store (MapType1Select Mask@5 this@@9 Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@5 this@@9 Node.valid) perm$R)) (Fractions 100))))))) (=> (and
(IsGoodMask Mask@6)
(IsGoodState (heapFragment (MapType2Select Heap@1 this@@9 Node.valid)))
(wf Heap@1 Mask@6 ZeroMask)
(wf Heap@1 Mask@6 ZeroMask)
(IsGoodMask Mask@6)
(wf Heap@1 Mask@6 ZeroMask)
(= |predVer#_20@0| (U_2_int (MapType2Select Heap@1 this@@9 Node.valid)))
(wf Heap@1 Mask@6 ZeroMask)) (and
(! (or %lbl%@29159 (= (|#Node.size| Heap@1 this@@9) 1)) :lblneg @29159)
(=> (= (|#Node.size| Heap@1 this@@9) 1) (and
(! (or %lbl%@29168 (> (Fractions 100) 0)) :lblneg @29168)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@29176 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@6 this@@9 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@6 this@@9 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@6 this@@9 Node.valid) perm$N)))))) :lblneg @29176)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@6 this@@9 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@6 this@@9 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@6 this@@9 Node.valid) perm$N))))) (=> (= |exhaleMask#_29@0| (MapType1Store Mask@6 this@@9 Node.valid (MapType0Store (MapType1Select Mask@6 this@@9 Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@6 this@@9 Node.valid) perm$R)) (Fractions 100)))))) (and
anon9_Then_correct
anon9_Else_correct))))))))))))))
(let ((anon8_Else_correct (=> (! (and %lbl%+3757 true) :lblpos +3757) (=> (and
(= (MapType2Select Heap@1 this@@9 Node.next) null)
(= Mask@5 Mask@3)) anon2_correct@@0))))
(let ((anon8_Then_correct (=> (! (and %lbl%+3755 true) :lblpos +3755) (=> (not (= (MapType2Select Heap@1 this@@9 Node.next) null)) (and
(! (or %lbl%@28882 (> (Fractions 100) 0)) :lblneg @28882)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@28890 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@3 (MapType2Select Heap@1 this@@9 Node.next) Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@3 (MapType2Select Heap@1 this@@9 Node.next) Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@3 (MapType2Select Heap@1 this@@9 Node.next) Node.valid) perm$N)))))) :lblneg @28890)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@3 (MapType2Select Heap@1 this@@9 Node.next) Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@3 (MapType2Select Heap@1 this@@9 Node.next) Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@3 (MapType2Select Heap@1 this@@9 Node.next) Node.valid) perm$N))))) (=> (= Mask@4 (MapType1Store Mask@3 (MapType2Select Heap@1 this@@9 Node.next) Node.valid (MapType0Store (MapType1Select Mask@3 (MapType2Select Heap@1 this@@9 Node.next) Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@3 (MapType2Select Heap@1 this@@9 Node.next) Node.valid) perm$R)) (Fractions 100)))))) (=> (and
(wf Heap@1 Mask@4 ZeroMask)
(= Mask@5 Mask@4)) anon2_correct@@0))))))))))
(let ((anon0_correct@@1 (=> (! (and %lbl%+3753 true) :lblpos +3753) (=> (and
(< 0 |methodK#_10@@0|)
(< (* 1000 |methodK#_10@@0|) (Fractions 1))
(= CurrentModule |module#default|)) (=> (and
CanAssumeFunctionDefs
(not (= this@@9 null))
(wf Heap@@7 ZeroMask ZeroMask)
(or
(= (MapType2Select Heap@@7 this@@9 Node.next) null)
(= (dtype (MapType2Select Heap@@7 this@@9 Node.next)) |Node#t|))
(> (Fractions 100) 0)
(= Mask@0@@0 (MapType1Store ZeroMask this@@9 Node.next (MapType0Store (MapType1Select ZeroMask this@@9 Node.next) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select ZeroMask this@@9 Node.next) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@0@@0)
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@9 Node.next)))) (=> (and
(wf Heap@@7 Mask@0@@0 ZeroMask)
(wf Heap@@7 Mask@0@@0 ZeroMask)
(not (= this@@9 null))
(wf Heap@@7 Mask@0@@0 ZeroMask)
(> (Fractions 100) 0)
(= Mask@1@@0 (MapType1Store Mask@0@@0 this@@9 Node.value (MapType0Store (MapType1Select Mask@0@@0 this@@9 Node.value) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@0@@0 this@@9 Node.value) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@1@@0)
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@9 Node.value)))
(wf Heap@@7 Mask@1@@0 ZeroMask)
(wf Heap@@7 Mask@1@@0 ZeroMask)
(IsGoodMask Mask@1@@0)
(wf Heap@@7 Mask@1@@0 ZeroMask)
(= Heap@@7 Heap@@7)
(= Mask@1@@0 Mask@@7)
(= ZeroMask SecMask@@7)
(= ZeroCredits Credits)) (and
(! (or %lbl%@28543 (CanWrite Mask@1@@0 this@@9 Node.next)) :lblneg @28543)
(=> (CanWrite Mask@1@@0 this@@9 Node.next) (=> (and
(= Heap@0@@0 (MapType2Store Heap@@7 this@@9 Node.next null))
(wf Heap@0@@0 Mask@1@@0 ZeroMask)) (and
(! (or %lbl%@28572 (CanWrite Mask@1@@0 this@@9 Node.value)) :lblneg @28572)
(=> (CanWrite Mask@1@@0 this@@9 Node.value) (=> (= Heap@1 (MapType2Store Heap@0@@0 this@@9 Node.value (int_2_U |v#0|))) (=> (and
(wf Heap@1 Mask@1@@0 ZeroMask)
(|#Node.valid#trigger| this@@9)) (=> (and
(< 0 |foldK#_22|)
(< (* 1000 |foldK#_22|) (Fractions 1))
(< (* 1000 |foldK#_22|) |methodK#_10@@0|)) (and
(! (or %lbl%@28636 (not (= this@@9 null))) :lblneg @28636)
(=> (not (= this@@9 null)) (and
(! (or %lbl%@28642 (> (Fractions 100) 0)) :lblneg @28642)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@28650 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@1@@0 this@@9 Node.next) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@1@@0 this@@9 Node.next) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@1@@0 this@@9 Node.next) perm$N)))))) :lblneg @28650)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@1@@0 this@@9 Node.next) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@1@@0 this@@9 Node.next) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@1@@0 this@@9 Node.next) perm$N))))) (=> (and
(= Mask@2@@0 (MapType1Store Mask@1@@0 this@@9 Node.next (MapType0Store (MapType1Select Mask@1@@0 this@@9 Node.next) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@1@@0 this@@9 Node.next) perm$R)) (Fractions 100))))))
(wf Heap@1 Mask@2@@0 ZeroMask)) (and
(! (or %lbl%@28750 (> (Fractions 100) 0)) :lblneg @28750)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@28758 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@2@@0 this@@9 Node.value) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@2@@0 this@@9 Node.value) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@2@@0 this@@9 Node.value) perm$N)))))) :lblneg @28758)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@2@@0 this@@9 Node.value) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@2@@0 this@@9 Node.value) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@2@@0 this@@9 Node.value) perm$N))))) (=> (and
(= Mask@3 (MapType1Store Mask@2@@0 this@@9 Node.value (MapType0Store (MapType1Select Mask@2@@0 this@@9 Node.value) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@2@@0 this@@9 Node.value) perm$R)) (Fractions 100))))))
(wf Heap@1 Mask@3 ZeroMask)) (and
anon8_Then_correct
anon8_Else_correct)))))))))))))))))))))))))))
(let ((PreconditionGeneratedEntry_correct@@1 (=> (! (and %lbl%+28164 true) :lblpos +28164) (=> (IsGoodMask Mask@@7) (=> (and
(IsGoodMask SecMask@@7)
(or
(= this@@9 null)
(= (dtype this@@9) |Node#t|))
(not (= this@@9 null))
(wf Heap@@7 Mask@@7 SecMask@@7)) anon0_correct@@1)))))
PreconditionGeneratedEntry_correct@@1)))))))))))))
))
(check-sat)
(pop 1)
(declare-fun |exhaleMask#_47@0| () T@U)
(declare-fun |fappSecMask#_43@0| () T@U)
(declare-fun this@@10 () T@U)
(declare-fun |fappHeap#_41@0| () T@U)
(declare-fun |exhaleHeap#_46@0| () T@U)
(declare-fun Heap@0@@1 () T@U)
(declare-fun |exhaleMask#_39@0| () T@U)
(declare-fun Mask@1@@1 () T@U)
(declare-fun |exhaleHeap#_38@0| () T@U)
(declare-fun |fappMask#_42@0| () T@U)
(declare-fun |fappCredits#_44@0| () T@U)
(declare-fun Mask@0@@1 () T@U)
(declare-fun %lbl%+4443 () Bool)
(declare-fun %lbl%+4441 () Bool)
(declare-fun %lbl%+4439 () Bool)
(declare-fun %lbl%+4437 () Bool)
(declare-fun %lbl%@30467 () Bool)
(declare-fun |funcappK#_45| () Int)
(declare-fun %lbl%@30537 () Bool)
(declare-fun %lbl%@30545 () Bool)
(declare-fun %lbl%+4433 () Bool)
(declare-fun %lbl%+4431 () Bool)
(declare-fun %lbl%+4429 () Bool)
(declare-fun |methodK#_32| () Int)
(declare-fun %lbl%@30028 () Bool)
(declare-fun %lbl%@30161 () Bool)
(declare-fun %lbl%@30252 () Bool)
(declare-fun |funcappK#_37| () Int)
(declare-fun %lbl%@30302 () Bool)
(declare-fun %lbl%@30310 () Bool)
(declare-fun %lbl%+29891 () Bool)
(assert (and
(= (type |exhaleMask#_47@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |fappSecMask#_43@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type this@@10) refType)
(= (type |fappHeap#_41@0|) (MapType2Type refType))
(= (type |exhaleHeap#_46@0|) (MapType2Type refType))
(= (type Heap@0@@1) (MapType2Type refType))
(= (type |exhaleMask#_39@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@1@@1) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |exhaleHeap#_38@0|) (MapType2Type refType))
(= (type |fappMask#_42@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |fappCredits#_44@0|) (MapType0Type refType intType))
(= (type Mask@0@@1) (MapType1Type refType (MapType0Type PermissionComponentType intType)))))
(push 1)
(set-info :boogie-vc-id Node.add$checkDefinedness)
(assert (not
(let ((anon4_correct@@0 (=> (! (and %lbl%+4443 true) :lblpos +4443) true)))
(let ((anon6_Else_correct (=> (! (and %lbl%+4441 true) :lblpos +4441) (=> (CanRead |exhaleMask#_47@0| |fappSecMask#_43@0| this@@10 Node.valid) anon4_correct@@0))))
(let ((anon6_Then_correct (=> (! (and %lbl%+4439 true) :lblpos +4439) (=> (and
(not (CanRead |exhaleMask#_47@0| |fappSecMask#_43@0| this@@10 Node.valid))
(< (U_2_int (MapType2Select |fappHeap#_41@0| this@@10 Node.valid)) (U_2_int (MapType2Select |exhaleHeap#_46@0| this@@10 Node.valid)))) anon4_correct@@0))))
(let ((anon2_correct@@1 (=> (! (and %lbl%+4437 true) :lblpos +4437) (=> (wf Heap@0@@1 |exhaleMask#_39@0| ZeroMask) (=> (and
(wf Heap@0@@1 Mask@1@@1 ZeroMask)
(IsGoodExhaleState |exhaleHeap#_38@0| Heap@0@@1 |exhaleMask#_39@0| ZeroMask)
(IsGoodMask |exhaleMask#_39@0|)
(wf |exhaleHeap#_38@0| |exhaleMask#_39@0| ZeroMask)) (and
(! (or %lbl%@30467 (=> true (not (= this@@10 null)))) :lblneg @30467)
(=> (=> true (not (= this@@10 null))) (=> (and
(< 0 |funcappK#_45|)
(< (* 1000 |funcappK#_45|) (Fractions 1))
(= |fappHeap#_41@0| Heap@@7)
(= |fappMask#_42@0| Mask@@7)
(= |fappSecMask#_43@0| SecMask@@7)
(= |fappCredits#_44@0| Credits)
(wf |fappHeap#_41@0| |fappMask#_42@0| |fappSecMask#_43@0|)) (and
(! (or %lbl%@30537 (> (Fractions 100) 0)) :lblneg @30537)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@30545 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |fappMask#_42@0| this@@10 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |fappMask#_42@0| this@@10 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select |fappMask#_42@0| this@@10 Node.valid) perm$N)))))) :lblneg @30545)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |fappMask#_42@0| this@@10 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |fappMask#_42@0| this@@10 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select |fappMask#_42@0| this@@10 Node.valid) perm$N))))) (=> (= |exhaleMask#_47@0| (MapType1Store |fappMask#_42@0| this@@10 Node.valid (MapType0Store (MapType1Select |fappMask#_42@0| this@@10 Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select |fappMask#_42@0| this@@10 Node.valid) perm$R)) (Fractions 100)))))) (and
anon6_Then_correct
anon6_Else_correct))))))))))))))
(let ((anon5_Else_correct (=> (! (and %lbl%+4433 true) :lblpos +4433) (=> (CanRead |exhaleMask#_39@0| ZeroMask this@@10 Node.valid) anon2_correct@@1))))
(let ((anon5_Then_correct (=> (! (and %lbl%+4431 true) :lblpos +4431) (=> (and
(not (CanRead |exhaleMask#_39@0| ZeroMask this@@10 Node.valid))
(< (U_2_int (MapType2Select Heap@0@@1 this@@10 Node.valid)) (U_2_int (MapType2Select |exhaleHeap#_38@0| this@@10 Node.valid)))) anon2_correct@@1))))
(let ((anon0_correct@@2 (=> (! (and %lbl%+4429 true) :lblpos +4429) (=> (and
(< 0 |methodK#_32|)
(< (* 1000 |methodK#_32|) (Fractions 1))
CanAssumeFunctionDefs) (and
(! (or %lbl%@30028 (not (= this@@10 null))) :lblneg @30028)
(=> (not (= this@@10 null)) (=> (and
(not (= this@@10 null))
(wf Heap@@7 ZeroMask ZeroMask)) (=> (and
(> (Fractions 100) 0)
(= Mask@0@@1 (MapType1Store ZeroMask this@@10 Node.valid (MapType0Store (MapType1Select ZeroMask this@@10 Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select ZeroMask this@@10 Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@0@@1)
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@10 Node.valid)))) (=> (and
(wf Heap@@7 Mask@0@@1 ZeroMask)
(wf Heap@@7 Mask@0@@1 ZeroMask)
(IsGoodMask Mask@0@@1)
(wf Heap@@7 Mask@0@@1 ZeroMask)
(= Heap@@7 Heap@@7)
(= Mask@0@@1 Mask@@7)
(= ZeroMask SecMask@@7)
(= ZeroCredits Credits)) (and
(! (or %lbl%@30161 (not (= this@@10 null))) :lblneg @30161)
(=> (not (= this@@10 null)) (=> (and
(not (= this@@10 null))
(wf Heap@0@@1 ZeroMask ZeroMask)
(> (Fractions 100) 0)
(= Mask@1@@1 (MapType1Store ZeroMask this@@10 Node.valid (MapType0Store (MapType1Select ZeroMask this@@10 Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select ZeroMask this@@10 Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@1@@1)
(IsGoodState (heapFragment (MapType2Select Heap@0@@1 this@@10 Node.valid)))
(wf Heap@0@@1 Mask@1@@1 ZeroMask)
(wf Heap@0@@1 Mask@1@@1 ZeroMask)) (and
(! (or %lbl%@30252 (=> true (not (= this@@10 null)))) :lblneg @30252)
(=> (=> true (not (= this@@10 null))) (=> (and
(< 0 |funcappK#_37|)
(< (* 1000 |funcappK#_37|) (Fractions 1))
(wf Heap@0@@1 Mask@1@@1 ZeroMask)) (and
(! (or %lbl%@30302 (> (Fractions 100) 0)) :lblneg @30302)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@30310 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@1@@1 this@@10 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@1@@1 this@@10 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@1@@1 this@@10 Node.valid) perm$N)))))) :lblneg @30310)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@1@@1 this@@10 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@1@@1 this@@10 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@1@@1 this@@10 Node.valid) perm$N))))) (=> (= |exhaleMask#_39@0| (MapType1Store Mask@1@@1 this@@10 Node.valid (MapType0Store (MapType1Select Mask@1@@1 this@@10 Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@1@@1 this@@10 Node.valid) perm$R)) (Fractions 100)))))) (and
anon5_Then_correct
anon5_Else_correct)))))))))))))))))))))
(let ((PreconditionGeneratedEntry_correct@@2 (=> (! (and %lbl%+29891 true) :lblpos +29891) (=> (IsGoodMask Mask@@7) (=> (and
(IsGoodMask SecMask@@7)
(or
(= this@@10 null)
(= (dtype this@@10) |Node#t|))
(not (= this@@10 null))
(wf Heap@@7 Mask@@7 SecMask@@7)) anon0_correct@@2)))))
PreconditionGeneratedEntry_correct@@2))))))))
))
(check-sat)
(pop 1)
(declare-fun |exhaleMask#_88@0| () T@U)
(declare-fun |exhaleHeap#_87@4| () T@U)
(declare-fun Heap@3 () T@U)
(declare-fun this@@11 () T@U)
(declare-fun |exhaleHeap#_87@3| () T@U)
(declare-fun |exhaleHeap#_87@2| () T@U)
(declare-fun |exhaleHeap#_87@1| () T@U)
(declare-fun |exhaleHeap#_87@0| () T@U)
(declare-fun Mask@16 () T@U)
(declare-fun Mask@15 () T@U)
(declare-fun Mask@13 () T@U)
(declare-fun Mask@14 () T@U)
(declare-fun Mask@11 () T@U)
(declare-fun Mask@12 () T@U)
(declare-fun |nw#_56@0| () T@U)
(declare-fun Mask@5@@0 () T@U)
(declare-fun Heap@1@@0 () T@U)
(declare-fun Mask@6@@0 () T@U)
(declare-fun Mask@7 () T@U)
(declare-fun Mask@8 () T@U)
(declare-fun |exhaleMask#_63@0| () T@U)
(declare-fun |exhaleMask#_63@1| () T@U)
(declare-fun |exhaleHeap#_62@0| () T@U)
(declare-fun Mask@9 () T@U)
(declare-fun Heap@2 () T@U)
(declare-fun |exhaleMask#_74@0| () T@U)
(declare-fun |exhaleHeap#_73@0| () T@U)
(declare-fun |this#11@0| () T@U)
(declare-fun Mask@10 () T@U)
(declare-fun Mask@3@@0 () T@U)
(declare-fun Mask@4@@0 () T@U)
(declare-fun Mask@1@@2 () T@U)
(declare-fun Mask@2@@1 () T@U)
(declare-fun Heap@0@@2 () T@U)
(declare-fun Mask@0@@2 () T@U)
(declare-fun |n#3| () T@U)
(declare-fun |this#9| () T@U)
(declare-fun |this#11| () T@U)
(declare-fun %lbl%+6539 () Bool)
(declare-fun %lbl%@33757 () Bool)
(declare-fun %lbl%@33823 () Bool)
(declare-fun ch@@5 () T@U)
(declare-fun %lbl%+6537 () Bool)
(declare-fun %lbl%+6535 () Bool)
(declare-fun %lbl%+6533 () Bool)
(declare-fun %lbl%+6531 () Bool)
(declare-fun %lbl%+6527 () Bool)
(declare-fun %lbl%+6522 () Bool)
(declare-fun %lbl%+6520 () Bool)
(declare-fun %lbl%+6518 () Bool)
(declare-fun |predVer#_79@0| () Int)
(declare-fun %lbl%@33457 () Bool)
(declare-fun %lbl%@33473 () Bool)
(declare-fun %lbl%@33481 () Bool)
(declare-fun %lbl%+6514 () Bool)
(declare-fun %lbl%+6512 () Bool)
(declare-fun %lbl%@33169 () Bool)
(declare-fun %lbl%@33177 () Bool)
(declare-fun %lbl%+6510 () Bool)
(declare-fun |foldK#_81| () Int)
(declare-fun |methodK#_32@@0| () Int)
(declare-fun %lbl%@32934 () Bool)
(declare-fun %lbl%@32940 () Bool)
(declare-fun %lbl%@32948 () Bool)
(declare-fun %lbl%@33048 () Bool)
(declare-fun %lbl%@33056 () Bool)
(declare-fun %lbl%+6506 () Bool)
(declare-fun %lbl%+6504 () Bool)
(declare-fun %lbl%+6502 () Bool)
(declare-fun %lbl%+6500 () Bool)
(declare-fun |cond#_55@0| () Bool)
(declare-fun |methodCallK#_72| () Int)
(declare-fun %lbl%@32569 () Bool)
(declare-fun %lbl%@32579 () Bool)
(declare-fun %lbl%@32591 () Bool)
(declare-fun %lbl%@32623 () Bool)
(declare-fun %lbl%@32631 () Bool)
(declare-fun %lbl%+6496 () Bool)
(declare-fun |methodCallK#_61| () Int)
(declare-fun %lbl%@32151 () Bool)
(declare-fun %lbl%@32166 () Bool)
(declare-fun %lbl%@32174 () Bool)
(declare-fun %lbl%@32273 () Bool)
(declare-fun %lbl%@32281 () Bool)
(declare-fun %lbl%@32494 () Bool)
(declare-fun %lbl%+6494 () Bool)
(declare-fun %lbl%@31884 () Bool)
(declare-fun %lbl%@31894 () Bool)
(declare-fun %lbl%+6489 () Bool)
(declare-fun %lbl%+6487 () Bool)
(declare-fun %lbl%+6485 () Bool)
(declare-fun %lbl%+6481 () Bool)
(declare-fun %lbl%+6479 () Bool)
(declare-fun |oldVers#_53@0| () Int)
(declare-fun |newVers#_54@0| () Int)
(declare-fun %lbl%+6477 () Bool)
(declare-fun |unfoldK#_49| () Int)
(declare-fun %lbl%@31325 () Bool)
(declare-fun %lbl%@31331 () Bool)
(declare-fun %lbl%@31339 () Bool)
(declare-fun %lbl%+30906 () Bool)
(assert (and
(= (type |exhaleMask#_88@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |exhaleHeap#_87@4|) (MapType2Type refType))
(= (type Heap@3) (MapType2Type refType))
(= (type this@@11) refType)
(= (type |exhaleHeap#_87@3|) (MapType2Type refType))
(= (type |exhaleHeap#_87@2|) (MapType2Type refType))
(= (type |exhaleHeap#_87@1|) (MapType2Type refType))
(= (type |exhaleHeap#_87@0|) (MapType2Type refType))
(= (type Mask@16) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@15) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@13) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@14) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@11) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@12) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |nw#_56@0|) refType)
(= (type Mask@5@@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Heap@1@@0) (MapType2Type refType))
(= (type Mask@6@@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@7) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@8) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |exhaleMask#_63@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |exhaleMask#_63@1|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |exhaleHeap#_62@0|) (MapType2Type refType))
(= (type Mask@9) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Heap@2) (MapType2Type refType))
(= (type |exhaleMask#_74@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |exhaleHeap#_73@0|) (MapType2Type refType))
(= (type |this#11@0|) refType)
(= (type Mask@10) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@3@@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@4@@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@1@@2) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@2@@1) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Heap@0@@2) (MapType2Type refType))
(= (type Mask@0@@2) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |n#3|) refType)
(= (type |this#9|) refType)
(= (type |this#11|) refType)))
(push 1)
(set-info :boogie-vc-id Node.add)
(assert (not
(let ((anon16_correct (=> (! (and %lbl%+6539 true) :lblpos +6539) (=> (and
(IsGoodMask |exhaleMask#_88@0|)
(wf |exhaleHeap#_87@4| |exhaleMask#_88@0| ZeroMask)) (and
(! (or %lbl%@33757 (forall ((|lk#_90| T@U) ) (! (=> (= (type |lk#_90|) refType) (or
(and
(iff (< 0 (U_2_int (MapType2Select |exhaleHeap#_87@4| |lk#_90| held))) (< 0 (U_2_int (MapType2Select Heap@@7 |lk#_90| held))))
(iff (U_2_bool (MapType2Select |exhaleHeap#_87@4| |lk#_90| rdheld)) (U_2_bool (MapType2Select Heap@@7 |lk#_90| rdheld))))
false))
 :qid |crashbpl.879:79|
 :skolemid |52|
 :pattern ( (MapType2Select |exhaleHeap#_87@4| |lk#_90| held))
 :pattern ( (MapType2Select |exhaleHeap#_87@4| |lk#_90| rdheld))
))) :lblneg @33757)
(=> (forall ((|lk#_90@@0| T@U) ) (! (=> (= (type |lk#_90@@0|) refType) (or
(and
(iff (< 0 (U_2_int (MapType2Select |exhaleHeap#_87@4| |lk#_90@@0| held))) (< 0 (U_2_int (MapType2Select Heap@@7 |lk#_90@@0| held))))
(iff (U_2_bool (MapType2Select |exhaleHeap#_87@4| |lk#_90@@0| rdheld)) (U_2_bool (MapType2Select Heap@@7 |lk#_90@@0| rdheld))))
false))
 :qid |crashbpl.879:79|
 :skolemid |52|
 :pattern ( (MapType2Select |exhaleHeap#_87@4| |lk#_90@@0| held))
 :pattern ( (MapType2Select |exhaleHeap#_87@4| |lk#_90@@0| rdheld))
)) (and
(! (or %lbl%@33823 (forall ((ch@@6 T@U) ) (! (=> (= (type ch@@6) refType) (or
(= ch@@6 null)
(<= 0 (U_2_int (MapType0Select ZeroCredits ch@@6)))))
 :qid |crashbpl.880:81|
 :skolemid |53|
 :no-pattern (type ch@@6)
 :no-pattern (U_2_int ch@@6)
 :no-pattern (U_2_bool ch@@6)
))) :lblneg @33823)
(=> (forall ((ch@@7 T@U) ) (! (=> (= (type ch@@7) refType) (or
(= ch@@7 null)
(<= 0 (U_2_int (MapType0Select ZeroCredits ch@@7)))))
 :qid |crashbpl.880:81|
 :skolemid |53|
 :no-pattern (type@@0 ch@@5)
 :no-pattern (type ch@@7)
 :no-pattern (U_2_int ch@@7)
 :no-pattern (U_2_bool ch@@7)
)) true))))))))
(let ((anon23_Else_correct (=> (! (and %lbl%+6537 true) :lblpos +6537) (=> (and
(not (CanRead |exhaleMask#_88@0| ZeroMask this@@11 Node.valid))
(= |exhaleHeap#_87@4| |exhaleHeap#_87@0|)) anon16_correct))))
(let ((anon24_Else_correct (=> (! (and %lbl%+6535 true) :lblpos +6535) (=> (and
(= (MapType2Select Heap@3 this@@11 Node.next) null)
(= |exhaleHeap#_87@4| |exhaleHeap#_87@2|)) anon16_correct))))
(let ((anon24_Then_correct (=> (! (and %lbl%+6533 true) :lblpos +6533) (=> (not (= (MapType2Select Heap@3 this@@11 Node.next) null)) (=> (and
(= |exhaleHeap#_87@3| (MapType2Store |exhaleHeap#_87@2| (MapType2Select Heap@3 this@@11 Node.next) Node.valid (MapType2Select Heap@3 (MapType2Select Heap@3 this@@11 Node.next) Node.valid)))
(= |exhaleHeap#_87@4| |exhaleHeap#_87@3|)) anon16_correct)))))
(let ((anon23_Then_correct (=> (! (and %lbl%+6531 true) :lblpos +6531) (=> (CanRead |exhaleMask#_88@0| ZeroMask this@@11 Node.valid) (=> (and
(= |exhaleHeap#_87@1| (MapType2Store |exhaleHeap#_87@0| this@@11 Node.next (MapType2Select Heap@3 this@@11 Node.next)))
(= |exhaleHeap#_87@2| (MapType2Store |exhaleHeap#_87@1| this@@11 Node.value (MapType2Select Heap@3 this@@11 Node.value)))) (and
anon24_Then_correct
anon24_Else_correct))))))
(let ((anon13_correct (=> (! (and %lbl%+6527 true) :lblpos +6527) (=> (wf Heap@3 |exhaleMask#_88@0| ZeroMask) (=> (and
(wf Heap@3 Mask@16 ZeroMask)
(IsGoodExhaleState |exhaleHeap#_87@0| Heap@3 |exhaleMask#_88@0| ZeroMask)) (and
anon23_Then_correct
anon23_Else_correct))))))
(let ((anon22_Else_correct (=> (! (and %lbl%+6522 true) :lblpos +6522) (=> (CanRead |exhaleMask#_88@0| ZeroMask this@@11 Node.valid) anon13_correct))))
(let ((anon22_Then_correct (=> (! (and %lbl%+6520 true) :lblpos +6520) (=> (and
(not (CanRead |exhaleMask#_88@0| ZeroMask this@@11 Node.valid))
(< (U_2_int (MapType2Select Heap@3 this@@11 Node.valid)) (U_2_int (MapType2Select |exhaleHeap#_87@0| this@@11 Node.valid)))) anon13_correct))))
(let ((anon11_correct (=> (! (and %lbl%+6518 true) :lblpos +6518) (=> (and
(IsGoodMask Mask@15)
(wf Heap@3 Mask@15 ZeroMask)) (=> (and
(not (= this@@11 null))
(wf Heap@3 Mask@15 ZeroMask)
(> (Fractions 100) 0)
(= Mask@16 (MapType1Store Mask@15 this@@11 Node.valid (MapType0Store (MapType1Select Mask@15 this@@11 Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@15 this@@11 Node.valid) perm$R)) (Fractions 100))))))) (=> (and
(IsGoodMask Mask@16)
(IsGoodState (heapFragment (MapType2Select Heap@3 this@@11 Node.valid)))
(wf Heap@3 Mask@16 ZeroMask)
(wf Heap@3 Mask@16 ZeroMask)
(IsGoodMask Mask@16)
(wf Heap@3 Mask@16 ZeroMask)
(= |predVer#_79@0| (U_2_int (MapType2Select Heap@3 this@@11 Node.valid)))
(wf Heap@3 Mask@16 ZeroMask)) (and
(! (or %lbl%@33457 (= (|#Node.size| Heap@3 this@@11) (+ (|#Node.size| Heap@@7 this@@11) 1))) :lblneg @33457)
(=> (= (|#Node.size| Heap@3 this@@11) (+ (|#Node.size| Heap@@7 this@@11) 1)) (and
(! (or %lbl%@33473 (> (Fractions 100) 0)) :lblneg @33473)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@33481 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@16 this@@11 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@16 this@@11 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@16 this@@11 Node.valid) perm$N)))))) :lblneg @33481)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@16 this@@11 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@16 this@@11 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@16 this@@11 Node.valid) perm$N))))) (=> (= |exhaleMask#_88@0| (MapType1Store Mask@16 this@@11 Node.valid (MapType0Store (MapType1Select Mask@16 this@@11 Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@16 this@@11 Node.valid) perm$R)) (Fractions 100)))))) (and
anon22_Then_correct
anon22_Else_correct))))))))))))))
(let ((anon21_Else_correct (=> (! (and %lbl%+6514 true) :lblpos +6514) (=> (and
(= (MapType2Select Heap@3 this@@11 Node.next) null)
(= Mask@15 Mask@13)) anon11_correct))))
(let ((anon21_Then_correct (=> (! (and %lbl%+6512 true) :lblpos +6512) (=> (not (= (MapType2Select Heap@3 this@@11 Node.next) null)) (and
(! (or %lbl%@33169 (> (Fractions 100) 0)) :lblneg @33169)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@33177 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@13 (MapType2Select Heap@3 this@@11 Node.next) Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@13 (MapType2Select Heap@3 this@@11 Node.next) Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@13 (MapType2Select Heap@3 this@@11 Node.next) Node.valid) perm$N)))))) :lblneg @33177)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@13 (MapType2Select Heap@3 this@@11 Node.next) Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@13 (MapType2Select Heap@3 this@@11 Node.next) Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@13 (MapType2Select Heap@3 this@@11 Node.next) Node.valid) perm$N))))) (=> (= Mask@14 (MapType1Store Mask@13 (MapType2Select Heap@3 this@@11 Node.next) Node.valid (MapType0Store (MapType1Select Mask@13 (MapType2Select Heap@3 this@@11 Node.next) Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@13 (MapType2Select Heap@3 this@@11 Node.next) Node.valid) perm$R)) (Fractions 100)))))) (=> (and
(wf Heap@3 Mask@14 ZeroMask)
(= Mask@15 Mask@14)) anon11_correct))))))))))
(let ((anon9_correct (=> (! (and %lbl%+6510 true) :lblpos +6510) (=> (|#Node.valid#trigger| this@@11) (=> (and
(< 0 |foldK#_81|)
(< (* 1000 |foldK#_81|) (Fractions 1))
(< (* 1000 |foldK#_81|) |methodK#_32@@0|)) (and
(! (or %lbl%@32934 (not (= this@@11 null))) :lblneg @32934)
(=> (not (= this@@11 null)) (and
(! (or %lbl%@32940 (> (Fractions 100) 0)) :lblneg @32940)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@32948 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@11 this@@11 Node.next) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@11 this@@11 Node.next) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@11 this@@11 Node.next) perm$N)))))) :lblneg @32948)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@11 this@@11 Node.next) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@11 this@@11 Node.next) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@11 this@@11 Node.next) perm$N))))) (=> (and
(= Mask@12 (MapType1Store Mask@11 this@@11 Node.next (MapType0Store (MapType1Select Mask@11 this@@11 Node.next) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@11 this@@11 Node.next) perm$R)) (Fractions 100))))))
(wf Heap@3 Mask@12 ZeroMask)) (and
(! (or %lbl%@33048 (> (Fractions 100) 0)) :lblneg @33048)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@33056 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@12 this@@11 Node.value) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@12 this@@11 Node.value) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@12 this@@11 Node.value) perm$N)))))) :lblneg @33056)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@12 this@@11 Node.value) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@12 this@@11 Node.value) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@12 this@@11 Node.value) perm$N))))) (=> (and
(= Mask@13 (MapType1Store Mask@12 this@@11 Node.value (MapType0Store (MapType1Select Mask@12 this@@11 Node.value) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@12 this@@11 Node.value) perm$R)) (Fractions 100))))))
(wf Heap@3 Mask@13 ZeroMask)) (and
anon21_Then_correct
anon21_Else_correct))))))))))))))))))
(let ((anon8_correct (=> (! (and %lbl%+6506 true) :lblpos +6506) (=> (and
(wf Heap@1@@0 |exhaleMask#_74@0| ZeroMask)
(wf Heap@1@@0 Mask@5@@0 ZeroMask)) (=> (and
(IsGoodExhaleState |exhaleHeap#_73@0| Heap@1@@0 |exhaleMask#_74@0| ZeroMask)
(IsGoodMask |exhaleMask#_74@0|)
(wf |exhaleHeap#_73@0| |exhaleMask#_74@0| ZeroMask)
(not (= |this#11@0| null))
(wf |exhaleHeap#_73@0| |exhaleMask#_74@0| ZeroMask)
(> (Fractions 100) 0)
(= Mask@10 (MapType1Store |exhaleMask#_74@0| |this#11@0| Node.valid (MapType0Store (MapType1Select |exhaleMask#_74@0| |this#11@0| Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select |exhaleMask#_74@0| |this#11@0| Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@10)
(IsGoodState (heapFragment (MapType2Select |exhaleHeap#_73@0| |this#11@0| Node.valid)))
(wf |exhaleHeap#_73@0| Mask@10 ZeroMask)
(wf |exhaleHeap#_73@0| Mask@10 ZeroMask)
(= (|#Node.size| |exhaleHeap#_73@0| |this#11@0|) (+ (|#Node.size| Heap@1@@0 |this#11@0|) 1))
(IsGoodMask Mask@10)
(wf |exhaleHeap#_73@0| Mask@10 ZeroMask)
(= Heap@3 |exhaleHeap#_73@0|)
(= Mask@11 Mask@10)) anon9_correct)))))
(let ((anon20_Else_correct (=> (! (and %lbl%+6504 true) :lblpos +6504) (=> (CanRead |exhaleMask#_74@0| ZeroMask |this#11@0| Node.valid) anon8_correct))))
(let ((anon20_Then_correct (=> (! (and %lbl%+6502 true) :lblpos +6502) (=> (and
(not (CanRead |exhaleMask#_74@0| ZeroMask |this#11@0| Node.valid))
(< (U_2_int (MapType2Select Heap@1@@0 |this#11@0| Node.valid)) (U_2_int (MapType2Select |exhaleHeap#_73@0| |this#11@0| Node.valid)))) anon8_correct))))
(let ((anon19_Else_correct (=> (! (and %lbl%+6500 true) :lblpos +6500) (=> (not |cond#_55@0|) (=> (and
(< 0 |methodCallK#_72|)
(< (* 1000 |methodCallK#_72|) (Fractions 1))
(< (* 1000 |methodCallK#_72|) |methodK#_32@@0|)
(wf Heap@1@@0 Mask@5@@0 ZeroMask)) (and
(! (or %lbl%@32569 (=> true (not (= this@@11 null)))) :lblneg @32569)
(=> (=> true (not (= this@@11 null))) (and
(! (or %lbl%@32579 (=> true (CanRead Mask@5@@0 ZeroMask this@@11 Node.next))) :lblneg @32579)
(=> (=> true (CanRead Mask@5@@0 ZeroMask this@@11 Node.next)) (and
(! (or %lbl%@32591 (not (= (MapType2Select Heap@1@@0 this@@11 Node.next) null))) :lblneg @32591)
(=> (not (= (MapType2Select Heap@1@@0 this@@11 Node.next) null)) (=> (= |this#11@0| (MapType2Select Heap@1@@0 this@@11 Node.next)) (and
(! (or %lbl%@32623 (> (Fractions 100) 0)) :lblneg @32623)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@32631 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@5@@0 |this#11@0| Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@5@@0 |this#11@0| Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@5@@0 |this#11@0| Node.valid) perm$N)))))) :lblneg @32631)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@5@@0 |this#11@0| Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@5@@0 |this#11@0| Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@5@@0 |this#11@0| Node.valid) perm$N))))) (=> (= |exhaleMask#_74@0| (MapType1Store Mask@5@@0 |this#11@0| Node.valid (MapType0Store (MapType1Select Mask@5@@0 |this#11@0| Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@5@@0 |this#11@0| Node.valid) perm$R)) (Fractions 100)))))) (and
anon20_Then_correct
anon20_Else_correct))))))))))))))))))
(let ((anon19_Then_correct (=> (! (and %lbl%+6496 true) :lblpos +6496) (=> |cond#_55@0| (=> (and
(not (= |nw#_56@0| null))
(= (dtype |nw#_56@0|) |Node#t|)
(forall ((f@@16 T@U) ) (! (let ((|T#_0| (FieldTypeInv0 (type f@@16))))
(=> (= (type f@@16) (FieldType |T#_0|)) (and
(= (U_2_int (MapType0Select (MapType1Select Mask@5@@0 |nw#_56@0| f@@16) perm$R)) 0)
(= (U_2_int (MapType0Select (MapType1Select Mask@5@@0 |nw#_56@0| f@@16) perm$N)) 0))))
 :qid |crashbpl.718:26|
 :skolemid |51|
 :no-pattern (type f@@16)
 :no-pattern (U_2_int f@@16)
 :no-pattern (U_2_bool f@@16)
))
(= (MapType2Select Heap@1@@0 |nw#_56@0| mu) $LockBottom)
(<= (U_2_int (MapType2Select Heap@1@@0 |nw#_56@0| held)) 0)
(iff (U_2_bool (MapType2Select Heap@1@@0 |nw#_56@0| rdheld)) false)
(= Mask@6@@0 (MapType1Store Mask@5@@0 |nw#_56@0| Node.next (MapType0Store (MapType1Select Mask@5@@0 |nw#_56@0| Node.next) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@5@@0 |nw#_56@0| Node.next) perm$R)) (Fractions 100))))))
(= Mask@7 (MapType1Store Mask@6@@0 |nw#_56@0| Node.value (MapType0Store (MapType1Select Mask@6@@0 |nw#_56@0| Node.value) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@6@@0 |nw#_56@0| Node.value) perm$R)) (Fractions 100))))))
(= Mask@8 (MapType1Store Mask@7 |nw#_56@0| mu (MapType0Store (MapType1Select Mask@7 |nw#_56@0| mu) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@7 |nw#_56@0| mu) perm$R)) (Fractions 100))))))
(< 0 |methodCallK#_61|)
(< (* 1000 |methodCallK#_61|) (Fractions 1))
(< (* 1000 |methodCallK#_61|) |methodK#_32@@0|)
(wf Heap@1@@0 Mask@8 ZeroMask)) (and
(! (or %lbl%@32151 (not (= |nw#_56@0| null))) :lblneg @32151)
(=> (not (= |nw#_56@0| null)) (and
(! (or %lbl%@32166 (> (Fractions 100) 0)) :lblneg @32166)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@32174 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@8 |nw#_56@0| Node.next) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@8 |nw#_56@0| Node.next) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@8 |nw#_56@0| Node.next) perm$N)))))) :lblneg @32174)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@8 |nw#_56@0| Node.next) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@8 |nw#_56@0| Node.next) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@8 |nw#_56@0| Node.next) perm$N))))) (=> (= |exhaleMask#_63@0| (MapType1Store Mask@8 |nw#_56@0| Node.next (MapType0Store (MapType1Select Mask@8 |nw#_56@0| Node.next) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@8 |nw#_56@0| Node.next) perm$R)) (Fractions 100)))))) (=> (and
(wf Heap@1@@0 |exhaleMask#_63@0| ZeroMask)
(wf Heap@1@@0 Mask@8 ZeroMask)) (and
(! (or %lbl%@32273 (> (Fractions 100) 0)) :lblneg @32273)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@32281 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |exhaleMask#_63@0| |nw#_56@0| Node.value) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |exhaleMask#_63@0| |nw#_56@0| Node.value) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select |exhaleMask#_63@0| |nw#_56@0| Node.value) perm$N)))))) :lblneg @32281)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |exhaleMask#_63@0| |nw#_56@0| Node.value) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |exhaleMask#_63@0| |nw#_56@0| Node.value) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select |exhaleMask#_63@0| |nw#_56@0| Node.value) perm$N))))) (=> (= |exhaleMask#_63@1| (MapType1Store |exhaleMask#_63@0| |nw#_56@0| Node.value (MapType0Store (MapType1Select |exhaleMask#_63@0| |nw#_56@0| Node.value) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select |exhaleMask#_63@0| |nw#_56@0| Node.value) perm$R)) (Fractions 100)))))) (=> (and
(wf Heap@1@@0 |exhaleMask#_63@1| ZeroMask)
(wf Heap@1@@0 Mask@8 ZeroMask)
(IsGoodExhaleState |exhaleHeap#_62@0| Heap@1@@0 |exhaleMask#_63@1| ZeroMask)
(IsGoodMask |exhaleMask#_63@1|)
(wf |exhaleHeap#_62@0| |exhaleMask#_63@1| ZeroMask)
(not (= |nw#_56@0| null))
(wf |exhaleHeap#_62@0| |exhaleMask#_63@1| ZeroMask)
(> (Fractions 100) 0)
(= Mask@9 (MapType1Store |exhaleMask#_63@1| |nw#_56@0| Node.valid (MapType0Store (MapType1Select |exhaleMask#_63@1| |nw#_56@0| Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select |exhaleMask#_63@1| |nw#_56@0| Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@9)
(IsGoodState (heapFragment (MapType2Select |exhaleHeap#_62@0| |nw#_56@0| Node.valid)))
(wf |exhaleHeap#_62@0| Mask@9 ZeroMask)
(wf |exhaleHeap#_62@0| Mask@9 ZeroMask)
(= (|#Node.size| |exhaleHeap#_62@0| |nw#_56@0|) 1)
(IsGoodMask Mask@9)
(wf |exhaleHeap#_62@0| Mask@9 ZeroMask)) (and
(! (or %lbl%@32494 (CanWrite Mask@9 this@@11 Node.next)) :lblneg @32494)
(=> (CanWrite Mask@9 this@@11 Node.next) (=> (and
(= Heap@2 (MapType2Store |exhaleHeap#_62@0| this@@11 Node.next |nw#_56@0|))
(wf Heap@2 Mask@9 ZeroMask)
(= Heap@3 Heap@2)
(= Mask@11 Mask@9)) anon9_correct))))))))))))))))))))))
(let ((anon4_correct@@1 (=> (! (and %lbl%+6494 true) :lblpos +6494) (=> (IsGoodMask Mask@5@@0) (=> (and
(wf Heap@1@@0 Mask@5@@0 ZeroMask)
(iff |cond#_55@0| (= (MapType2Select Heap@1@@0 this@@11 Node.next) null))) (and
(! (or %lbl%@31884 (=> true (not (= this@@11 null)))) :lblneg @31884)
(=> (=> true (not (= this@@11 null))) (and
(! (or %lbl%@31894 (=> true (CanRead Mask@5@@0 ZeroMask this@@11 Node.next))) :lblneg @31894)
(=> (=> true (CanRead Mask@5@@0 ZeroMask this@@11 Node.next)) (and
anon19_Then_correct
anon19_Else_correct))))))))))
(let ((anon18_Else_correct (=> (! (and %lbl%+6489 true) :lblpos +6489) (=> (and
(= (MapType2Select Heap@1@@0 this@@11 Node.next) null)
(= Mask@5@@0 Mask@3@@0)) anon4_correct@@1))))
(let ((anon18_Then_correct (=> (! (and %lbl%+6487 true) :lblpos +6487) (=> (and
(not (= (MapType2Select Heap@1@@0 this@@11 Node.next) null))
(not (= (MapType2Select Heap@1@@0 this@@11 Node.next) null))) (=> (and
(wf Heap@1@@0 Mask@3@@0 ZeroMask)
(> (Fractions 100) 0)
(= Mask@4@@0 (MapType1Store Mask@3@@0 (MapType2Select Heap@1@@0 this@@11 Node.next) Node.valid (MapType0Store (MapType1Select Mask@3@@0 (MapType2Select Heap@1@@0 this@@11 Node.next) Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@3@@0 (MapType2Select Heap@1@@0 this@@11 Node.next) Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@4@@0)
(IsGoodState (heapFragment (MapType2Select Heap@1@@0 (MapType2Select Heap@1@@0 this@@11 Node.next) Node.valid)))
(wf Heap@1@@0 Mask@4@@0 ZeroMask)
(wf Heap@1@@0 Mask@4@@0 ZeroMask)
(= Mask@5@@0 Mask@4@@0)) anon4_correct@@1)))))
(let ((anon2_correct@@2 (=> (! (and %lbl%+6485 true) :lblpos +6485) (=> (and
(wf Heap@1@@0 Mask@1@@2 ZeroMask)
(IsGoodMask Mask@1@@2)
(wf Heap@1@@0 Mask@1@@2 ZeroMask)
(not (= this@@11 null))) (=> (and
(wf Heap@1@@0 Mask@1@@2 ZeroMask)
(or
(= (MapType2Select Heap@1@@0 this@@11 Node.next) null)
(= (dtype (MapType2Select Heap@1@@0 this@@11 Node.next)) |Node#t|))
(> (Fractions 100) 0)
(= Mask@2@@1 (MapType1Store Mask@1@@2 this@@11 Node.next (MapType0Store (MapType1Select Mask@1@@2 this@@11 Node.next) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@1@@2 this@@11 Node.next) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@2@@1)
(IsGoodState (heapFragment (MapType2Select Heap@1@@0 this@@11 Node.next)))
(wf Heap@1@@0 Mask@2@@1 ZeroMask)
(wf Heap@1@@0 Mask@2@@1 ZeroMask)
(not (= this@@11 null))
(wf Heap@1@@0 Mask@2@@1 ZeroMask)
(> (Fractions 100) 0)
(= Mask@3@@0 (MapType1Store Mask@2@@1 this@@11 Node.value (MapType0Store (MapType1Select Mask@2@@1 this@@11 Node.value) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@2@@1 this@@11 Node.value) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@3@@0)
(IsGoodState (heapFragment (MapType2Select Heap@1@@0 this@@11 Node.value)))
(wf Heap@1@@0 Mask@3@@0 ZeroMask)
(wf Heap@1@@0 Mask@3@@0 ZeroMask)) (and
anon18_Then_correct
anon18_Else_correct))))))
(let ((anon17_Else_correct (=> (! (and %lbl%+6481 true) :lblpos +6481) (=> (and
(CanRead Mask@1@@2 ZeroMask this@@11 Node.valid)
(= Heap@1@@0 Heap@@7)) anon2_correct@@2))))
(let ((anon17_Then_correct (=> (! (and %lbl%+6479 true) :lblpos +6479) (=> (not (CanRead Mask@1@@2 ZeroMask this@@11 Node.valid)) (=> (and
(= |oldVers#_53@0| (U_2_int (MapType2Select Heap@@7 this@@11 Node.valid)))
(= Heap@0@@2 (MapType2Store Heap@@7 this@@11 Node.valid (int_2_U |newVers#_54@0|)))
(< |oldVers#_53@0| (U_2_int (MapType2Select Heap@0@@2 this@@11 Node.valid)))
(= Heap@1@@0 Heap@0@@2)) anon2_correct@@2)))))
(let ((anon0_correct@@3 (=> (! (and %lbl%+6477 true) :lblpos +6477) (=> (and
(< 0 |methodK#_32@@0|)
(< (* 1000 |methodK#_32@@0|) (Fractions 1))
(= CurrentModule |module#default|)
CanAssumeFunctionDefs
(not (= this@@11 null))
(wf Heap@@7 ZeroMask ZeroMask)
(> (Fractions 100) 0)) (=> (and
(= Mask@0@@2 (MapType1Store ZeroMask this@@11 Node.valid (MapType0Store (MapType1Select ZeroMask this@@11 Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select ZeroMask this@@11 Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@0@@2)
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@11 Node.valid)))
(wf Heap@@7 Mask@0@@2 ZeroMask)
(wf Heap@@7 Mask@0@@2 ZeroMask)
(IsGoodMask Mask@0@@2)
(wf Heap@@7 Mask@0@@2 ZeroMask)
(= Heap@@7 Heap@@7)
(= Mask@0@@2 Mask@@7)
(= ZeroMask SecMask@@7)
(= ZeroCredits Credits)
(|#Node.valid#trigger| this@@11)
(< 0 |unfoldK#_49|)
(< |unfoldK#_49| (Fractions 1))
(< (* 1000 |unfoldK#_49|) |methodK#_32@@0|)) (and
(! (or %lbl%@31325 (not (= this@@11 null))) :lblneg @31325)
(=> (not (= this@@11 null)) (and
(! (or %lbl%@31331 (> (Fractions 100) 0)) :lblneg @31331)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@31339 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@2 this@@11 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@2 this@@11 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@0@@2 this@@11 Node.valid) perm$N)))))) :lblneg @31339)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@2 this@@11 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@2 this@@11 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@0@@2 this@@11 Node.valid) perm$N))))) (=> (= Mask@1@@2 (MapType1Store Mask@0@@2 this@@11 Node.valid (MapType0Store (MapType1Select Mask@0@@2 this@@11 Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@0@@2 this@@11 Node.valid) perm$R)) (Fractions 100)))))) (and
anon17_Then_correct
anon17_Else_correct)))))))))))))
(let ((PreconditionGeneratedEntry_correct@@3 (=> (! (and %lbl%+30906 true) :lblpos +30906) (=> (and
(IsGoodMask Mask@@7)
(IsGoodMask SecMask@@7)
(or
(= this@@11 null)
(= (dtype this@@11) |Node#t|))
(or
(= |n#3| null)
(= (dtype |n#3|) |Node#t|))
(or
(= |this#9| null)
(= (dtype |this#9|) |Node#t|))
(or
(= |this#11| null)
(= (dtype |this#11|) |Node#t|))
(not (= this@@11 null))
(wf Heap@@7 Mask@@7 SecMask@@7)) anon0_correct@@3))))
PreconditionGeneratedEntry_correct@@3)))))))))))))))))))))))))
))
(check-sat)
(pop 1)
(declare-fun |exhaleMask#_106@0| () T@U)
(declare-fun |fappSecMask#_102@0| () T@U)
(declare-fun this@@12 () T@U)
(declare-fun |fappHeap#_100@0| () T@U)
(declare-fun |exhaleHeap#_105@0| () T@U)
(declare-fun Heap@0@@3 () T@U)
(declare-fun |exhaleMask#_98@0| () T@U)
(declare-fun Mask@1@@3 () T@U)
(declare-fun |exhaleHeap#_97@0| () T@U)
(declare-fun |fappMask#_101@0| () T@U)
(declare-fun |fappCredits#_103@0| () T@U)
(declare-fun |rt#5| () T@U)
(declare-fun Mask@0@@3 () T@U)
(declare-fun %lbl%+7220 () Bool)
(declare-fun %lbl%+7218 () Bool)
(declare-fun %lbl%+7216 () Bool)
(declare-fun %lbl%+7214 () Bool)
(declare-fun %lbl%@35174 () Bool)
(declare-fun |funcappK#_104| () Int)
(declare-fun %lbl%@35244 () Bool)
(declare-fun %lbl%@35252 () Bool)
(declare-fun %lbl%+7210 () Bool)
(declare-fun %lbl%+7208 () Bool)
(declare-fun %lbl%+7206 () Bool)
(declare-fun |methodK#_91| () Int)
(declare-fun %lbl%@34727 () Bool)
(declare-fun %lbl%@34868 () Bool)
(declare-fun %lbl%@34959 () Bool)
(declare-fun |funcappK#_96| () Int)
(declare-fun %lbl%@35009 () Bool)
(declare-fun %lbl%@35017 () Bool)
(declare-fun %lbl%+34574 () Bool)
(assert (and
(= (type |exhaleMask#_106@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |fappSecMask#_102@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type this@@12) refType)
(= (type |fappHeap#_100@0|) (MapType2Type refType))
(= (type |exhaleHeap#_105@0|) (MapType2Type refType))
(= (type Heap@0@@3) (MapType2Type refType))
(= (type |exhaleMask#_98@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@1@@3) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |exhaleHeap#_97@0|) (MapType2Type refType))
(= (type |fappMask#_101@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |fappCredits#_103@0|) (MapType0Type refType intType))
(= (type |rt#5|) refType)
(= (type Mask@0@@3) (MapType1Type refType (MapType0Type PermissionComponentType intType)))))
(push 1)
(set-info :boogie-vc-id Node.addFirst$checkDefinedness)
(assert (not
(let ((anon4_correct@@2 (=> (! (and %lbl%+7220 true) :lblpos +7220) true)))
(let ((anon6_Else_correct@@0 (=> (! (and %lbl%+7218 true) :lblpos +7218) (=> (CanRead |exhaleMask#_106@0| |fappSecMask#_102@0| this@@12 Node.valid) anon4_correct@@2))))
(let ((anon6_Then_correct@@0 (=> (! (and %lbl%+7216 true) :lblpos +7216) (=> (and
(not (CanRead |exhaleMask#_106@0| |fappSecMask#_102@0| this@@12 Node.valid))
(< (U_2_int (MapType2Select |fappHeap#_100@0| this@@12 Node.valid)) (U_2_int (MapType2Select |exhaleHeap#_105@0| this@@12 Node.valid)))) anon4_correct@@2))))
(let ((anon2_correct@@3 (=> (! (and %lbl%+7214 true) :lblpos +7214) (=> (wf Heap@0@@3 |exhaleMask#_98@0| ZeroMask) (=> (and
(wf Heap@0@@3 Mask@1@@3 ZeroMask)
(IsGoodExhaleState |exhaleHeap#_97@0| Heap@0@@3 |exhaleMask#_98@0| ZeroMask)
(IsGoodMask |exhaleMask#_98@0|)
(wf |exhaleHeap#_97@0| |exhaleMask#_98@0| ZeroMask)) (and
(! (or %lbl%@35174 (=> true (not (= this@@12 null)))) :lblneg @35174)
(=> (=> true (not (= this@@12 null))) (=> (and
(< 0 |funcappK#_104|)
(< (* 1000 |funcappK#_104|) (Fractions 1))
(= |fappHeap#_100@0| Heap@@7)
(= |fappMask#_101@0| Mask@@7)
(= |fappSecMask#_102@0| SecMask@@7)
(= |fappCredits#_103@0| Credits)
(wf |fappHeap#_100@0| |fappMask#_101@0| |fappSecMask#_102@0|)) (and
(! (or %lbl%@35244 (> (Fractions 100) 0)) :lblneg @35244)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@35252 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |fappMask#_101@0| this@@12 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |fappMask#_101@0| this@@12 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select |fappMask#_101@0| this@@12 Node.valid) perm$N)))))) :lblneg @35252)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |fappMask#_101@0| this@@12 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |fappMask#_101@0| this@@12 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select |fappMask#_101@0| this@@12 Node.valid) perm$N))))) (=> (= |exhaleMask#_106@0| (MapType1Store |fappMask#_101@0| this@@12 Node.valid (MapType0Store (MapType1Select |fappMask#_101@0| this@@12 Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select |fappMask#_101@0| this@@12 Node.valid) perm$R)) (Fractions 100)))))) (and
anon6_Then_correct@@0
anon6_Else_correct@@0))))))))))))))
(let ((anon5_Else_correct@@0 (=> (! (and %lbl%+7210 true) :lblpos +7210) (=> (CanRead |exhaleMask#_98@0| ZeroMask |rt#5| Node.valid) anon2_correct@@3))))
(let ((anon5_Then_correct@@0 (=> (! (and %lbl%+7208 true) :lblpos +7208) (=> (and
(not (CanRead |exhaleMask#_98@0| ZeroMask |rt#5| Node.valid))
(< (U_2_int (MapType2Select Heap@0@@3 |rt#5| Node.valid)) (U_2_int (MapType2Select |exhaleHeap#_97@0| |rt#5| Node.valid)))) anon2_correct@@3))))
(let ((anon0_correct@@4 (=> (! (and %lbl%+7206 true) :lblpos +7206) (=> (and
(< 0 |methodK#_91|)
(< (* 1000 |methodK#_91|) (Fractions 1))
CanAssumeFunctionDefs) (and
(! (or %lbl%@34727 (not (= this@@12 null))) :lblneg @34727)
(=> (not (= this@@12 null)) (=> (not (= this@@12 null)) (=> (and
(wf Heap@@7 ZeroMask ZeroMask)
(> (Fractions 100) 0)) (=> (and
(= Mask@0@@3 (MapType1Store ZeroMask this@@12 Node.valid (MapType0Store (MapType1Select ZeroMask this@@12 Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select ZeroMask this@@12 Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@0@@3)
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@12 Node.valid)))
(wf Heap@@7 Mask@0@@3 ZeroMask)) (=> (and
(wf Heap@@7 Mask@0@@3 ZeroMask)
(IsGoodMask Mask@0@@3)
(wf Heap@@7 Mask@0@@3 ZeroMask)
(= Heap@@7 Heap@@7)
(= Mask@0@@3 Mask@@7)
(= ZeroMask SecMask@@7)
(= ZeroCredits Credits)
(not (= |rt#5| null))) (and
(! (or %lbl%@34868 (not (= |rt#5| null))) :lblneg @34868)
(=> (not (= |rt#5| null)) (=> (and
(not (= |rt#5| null))
(wf Heap@0@@3 ZeroMask ZeroMask)
(> (Fractions 100) 0)
(= Mask@1@@3 (MapType1Store ZeroMask |rt#5| Node.valid (MapType0Store (MapType1Select ZeroMask |rt#5| Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select ZeroMask |rt#5| Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@1@@3)
(IsGoodState (heapFragment (MapType2Select Heap@0@@3 |rt#5| Node.valid)))
(wf Heap@0@@3 Mask@1@@3 ZeroMask)
(wf Heap@0@@3 Mask@1@@3 ZeroMask)) (and
(! (or %lbl%@34959 (=> true (not (= |rt#5| null)))) :lblneg @34959)
(=> (=> true (not (= |rt#5| null))) (=> (and
(< 0 |funcappK#_96|)
(< (* 1000 |funcappK#_96|) (Fractions 1))
(wf Heap@0@@3 Mask@1@@3 ZeroMask)) (and
(! (or %lbl%@35009 (> (Fractions 100) 0)) :lblneg @35009)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@35017 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@1@@3 |rt#5| Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@1@@3 |rt#5| Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@1@@3 |rt#5| Node.valid) perm$N)))))) :lblneg @35017)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@1@@3 |rt#5| Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@1@@3 |rt#5| Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@1@@3 |rt#5| Node.valid) perm$N))))) (=> (= |exhaleMask#_98@0| (MapType1Store Mask@1@@3 |rt#5| Node.valid (MapType0Store (MapType1Select Mask@1@@3 |rt#5| Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@1@@3 |rt#5| Node.valid) perm$R)) (Fractions 100)))))) (and
anon5_Then_correct@@0
anon5_Else_correct@@0))))))))))))))))))))))
(let ((PreconditionGeneratedEntry_correct@@4 (=> (! (and %lbl%+34574 true) :lblpos +34574) (=> (and
(IsGoodMask Mask@@7)
(IsGoodMask SecMask@@7)) (=> (and
(or
(= this@@12 null)
(= (dtype this@@12) |Node#t|))
(or
(= |rt#5| null)
(= (dtype |rt#5|) |Node#t|))
(not (= this@@12 null))
(wf Heap@@7 Mask@@7 SecMask@@7)) anon0_correct@@4)))))
PreconditionGeneratedEntry_correct@@4))))))))
))
(check-sat)
(pop 1)
(declare-fun |exhaleMask#_119@0| () T@U)
(declare-fun |exhaleHeap#_118@4| () T@U)
(declare-fun Heap@1@@1 () T@U)
(declare-fun |nw#_108@0| () T@U)
(declare-fun |exhaleHeap#_118@3| () T@U)
(declare-fun |exhaleHeap#_118@2| () T@U)
(declare-fun |exhaleHeap#_118@1| () T@U)
(declare-fun |exhaleHeap#_118@0| () T@U)
(declare-fun Mask@8@@0 () T@U)
(declare-fun Mask@7@@0 () T@U)
(declare-fun this@@13 () T@U)
(declare-fun Mask@5@@1 () T@U)
(declare-fun Mask@6@@1 () T@U)
(declare-fun Mask@0@@4 () T@U)
(declare-fun Mask@1@@4 () T@U)
(declare-fun Mask@2@@2 () T@U)
(declare-fun Mask@3@@1 () T@U)
(declare-fun Heap@0@@4 () T@U)
(declare-fun Mask@4@@1 () T@U)
(declare-fun |rt#5@@0| () T@U)
(declare-fun |n#7| () T@U)
(declare-fun %lbl%+8240 () Bool)
(declare-fun %lbl%@37009 () Bool)
(declare-fun %lbl%@37075 () Bool)
(declare-fun ch@@8 () T@U)
(declare-fun %lbl%+8238 () Bool)
(declare-fun %lbl%+8236 () Bool)
(declare-fun %lbl%+8234 () Bool)
(declare-fun %lbl%+8232 () Bool)
(declare-fun %lbl%+8228 () Bool)
(declare-fun %lbl%+8223 () Bool)
(declare-fun %lbl%+8221 () Bool)
(declare-fun %lbl%+8219 () Bool)
(declare-fun |predVer#_110@0| () Int)
(declare-fun %lbl%@36713 () Bool)
(declare-fun %lbl%@36720 () Bool)
(declare-fun %lbl%@36735 () Bool)
(declare-fun %lbl%@36743 () Bool)
(declare-fun %lbl%+8215 () Bool)
(declare-fun %lbl%+8213 () Bool)
(declare-fun %lbl%@36447 () Bool)
(declare-fun %lbl%@36455 () Bool)
(declare-fun %lbl%+8211 () Bool)
(declare-fun |methodK#_91@@0| () Int)
(declare-fun %lbl%@36128 () Bool)
(declare-fun |x#4| () Int)
(declare-fun %lbl%@36155 () Bool)
(declare-fun |foldK#_112| () Int)
(declare-fun %lbl%@36216 () Bool)
(declare-fun %lbl%@36221 () Bool)
(declare-fun %lbl%@36229 () Bool)
(declare-fun %lbl%@36323 () Bool)
(declare-fun %lbl%@36331 () Bool)
(declare-fun %lbl%+35624 () Bool)
(assert (and
(= (type |exhaleMask#_119@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |exhaleHeap#_118@4|) (MapType2Type refType))
(= (type Heap@1@@1) (MapType2Type refType))
(= (type |nw#_108@0|) refType)
(= (type |exhaleHeap#_118@3|) (MapType2Type refType))
(= (type |exhaleHeap#_118@2|) (MapType2Type refType))
(= (type |exhaleHeap#_118@1|) (MapType2Type refType))
(= (type |exhaleHeap#_118@0|) (MapType2Type refType))
(= (type Mask@8@@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@7@@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type this@@13) refType)
(= (type Mask@5@@1) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@6@@1) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@0@@4) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@1@@4) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@2@@2) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@3@@1) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Heap@0@@4) (MapType2Type refType))
(= (type Mask@4@@1) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |rt#5@@0|) refType)
(= (type |n#7|) refType)))
(push 1)
(set-info :boogie-vc-id Node.addFirst)
(assert (not
(let ((anon7_correct@@0 (=> (! (and %lbl%+8240 true) :lblpos +8240) (=> (and
(IsGoodMask |exhaleMask#_119@0|)
(wf |exhaleHeap#_118@4| |exhaleMask#_119@0| ZeroMask)) (and
(! (or %lbl%@37009 (forall ((|lk#_121| T@U) ) (! (=> (= (type |lk#_121|) refType) (or
(and
(iff (< 0 (U_2_int (MapType2Select |exhaleHeap#_118@4| |lk#_121| held))) (< 0 (U_2_int (MapType2Select Heap@@7 |lk#_121| held))))
(iff (U_2_bool (MapType2Select |exhaleHeap#_118@4| |lk#_121| rdheld)) (U_2_bool (MapType2Select Heap@@7 |lk#_121| rdheld))))
false))
 :qid |crashbpl.1123:79|
 :skolemid |55|
 :pattern ( (MapType2Select |exhaleHeap#_118@4| |lk#_121| held))
 :pattern ( (MapType2Select |exhaleHeap#_118@4| |lk#_121| rdheld))
))) :lblneg @37009)
(=> (forall ((|lk#_121@@0| T@U) ) (! (=> (= (type |lk#_121@@0|) refType) (or
(and
(iff (< 0 (U_2_int (MapType2Select |exhaleHeap#_118@4| |lk#_121@@0| held))) (< 0 (U_2_int (MapType2Select Heap@@7 |lk#_121@@0| held))))
(iff (U_2_bool (MapType2Select |exhaleHeap#_118@4| |lk#_121@@0| rdheld)) (U_2_bool (MapType2Select Heap@@7 |lk#_121@@0| rdheld))))
false))
 :qid |crashbpl.1123:79|
 :skolemid |55|
 :pattern ( (MapType2Select |exhaleHeap#_118@4| |lk#_121@@0| held))
 :pattern ( (MapType2Select |exhaleHeap#_118@4| |lk#_121@@0| rdheld))
)) (and
(! (or %lbl%@37075 (forall ((ch@@9 T@U) ) (! (=> (= (type ch@@9) refType) (or
(= ch@@9 null)
(<= 0 (U_2_int (MapType0Select ZeroCredits ch@@9)))))
 :qid |crashbpl.1124:81|
 :skolemid |56|
 :no-pattern (type ch@@9)
 :no-pattern (U_2_int ch@@9)
 :no-pattern (U_2_bool ch@@9)
))) :lblneg @37075)
(=> (forall ((ch@@10 T@U) ) (! (=> (= (type ch@@10) refType) (or
(= ch@@10 null)
(<= 0 (U_2_int (MapType0Select ZeroCredits ch@@10)))))
 :qid |crashbpl.1124:81|
 :skolemid |56|
 :no-pattern (type@@0 ch@@8)
 :no-pattern (type ch@@10)
 :no-pattern (U_2_int ch@@10)
 :no-pattern (U_2_bool ch@@10)
)) true))))))))
(let ((anon10_Else_correct@@0 (=> (! (and %lbl%+8238 true) :lblpos +8238) (=> (and
(not (CanRead |exhaleMask#_119@0| ZeroMask |nw#_108@0| Node.valid))
(= |exhaleHeap#_118@4| |exhaleHeap#_118@0|)) anon7_correct@@0))))
(let ((anon11_Else_correct@@0 (=> (! (and %lbl%+8236 true) :lblpos +8236) (=> (and
(= (MapType2Select Heap@1@@1 |nw#_108@0| Node.next) null)
(= |exhaleHeap#_118@4| |exhaleHeap#_118@2|)) anon7_correct@@0))))
(let ((anon11_Then_correct@@0 (=> (! (and %lbl%+8234 true) :lblpos +8234) (=> (not (= (MapType2Select Heap@1@@1 |nw#_108@0| Node.next) null)) (=> (and
(= |exhaleHeap#_118@3| (MapType2Store |exhaleHeap#_118@2| (MapType2Select Heap@1@@1 |nw#_108@0| Node.next) Node.valid (MapType2Select Heap@1@@1 (MapType2Select Heap@1@@1 |nw#_108@0| Node.next) Node.valid)))
(= |exhaleHeap#_118@4| |exhaleHeap#_118@3|)) anon7_correct@@0)))))
(let ((anon10_Then_correct@@0 (=> (! (and %lbl%+8232 true) :lblpos +8232) (=> (CanRead |exhaleMask#_119@0| ZeroMask |nw#_108@0| Node.valid) (=> (and
(= |exhaleHeap#_118@1| (MapType2Store |exhaleHeap#_118@0| |nw#_108@0| Node.next (MapType2Select Heap@1@@1 |nw#_108@0| Node.next)))
(= |exhaleHeap#_118@2| (MapType2Store |exhaleHeap#_118@1| |nw#_108@0| Node.value (MapType2Select Heap@1@@1 |nw#_108@0| Node.value)))) (and
anon11_Then_correct@@0
anon11_Else_correct@@0))))))
(let ((anon4_correct@@3 (=> (! (and %lbl%+8228 true) :lblpos +8228) (=> (wf Heap@1@@1 |exhaleMask#_119@0| ZeroMask) (=> (and
(wf Heap@1@@1 Mask@8@@0 ZeroMask)
(IsGoodExhaleState |exhaleHeap#_118@0| Heap@1@@1 |exhaleMask#_119@0| ZeroMask)) (and
anon10_Then_correct@@0
anon10_Else_correct@@0))))))
(let ((anon9_Else_correct@@0 (=> (! (and %lbl%+8223 true) :lblpos +8223) (=> (CanRead |exhaleMask#_119@0| ZeroMask |nw#_108@0| Node.valid) anon4_correct@@3))))
(let ((anon9_Then_correct@@0 (=> (! (and %lbl%+8221 true) :lblpos +8221) (=> (and
(not (CanRead |exhaleMask#_119@0| ZeroMask |nw#_108@0| Node.valid))
(< (U_2_int (MapType2Select Heap@1@@1 |nw#_108@0| Node.valid)) (U_2_int (MapType2Select |exhaleHeap#_118@0| |nw#_108@0| Node.valid)))) anon4_correct@@3))))
(let ((anon2_correct@@4 (=> (! (and %lbl%+8219 true) :lblpos +8219) (=> (and
(IsGoodMask Mask@7@@0)
(wf Heap@1@@1 Mask@7@@0 ZeroMask)) (=> (and
(not (= |nw#_108@0| null))
(wf Heap@1@@1 Mask@7@@0 ZeroMask)
(> (Fractions 100) 0)
(= Mask@8@@0 (MapType1Store Mask@7@@0 |nw#_108@0| Node.valid (MapType0Store (MapType1Select Mask@7@@0 |nw#_108@0| Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@7@@0 |nw#_108@0| Node.valid) perm$R)) (Fractions 100))))))) (=> (and
(IsGoodMask Mask@8@@0)
(IsGoodState (heapFragment (MapType2Select Heap@1@@1 |nw#_108@0| Node.valid)))
(wf Heap@1@@1 Mask@8@@0 ZeroMask)
(wf Heap@1@@1 Mask@8@@0 ZeroMask)
(IsGoodMask Mask@8@@0)
(wf Heap@1@@1 Mask@8@@0 ZeroMask)
(= |predVer#_110@0| (U_2_int (MapType2Select Heap@1@@1 |nw#_108@0| Node.valid)))
(wf Heap@1@@1 Mask@8@@0 ZeroMask)) (and
(! (or %lbl%@36713 (not (= |nw#_108@0| null))) :lblneg @36713)
(=> (not (= |nw#_108@0| null)) (and
(! (or %lbl%@36720 (= (|#Node.size| Heap@1@@1 |nw#_108@0|) (+ (|#Node.size| Heap@@7 this@@13) 1))) :lblneg @36720)
(=> (= (|#Node.size| Heap@1@@1 |nw#_108@0|) (+ (|#Node.size| Heap@@7 this@@13) 1)) (and
(! (or %lbl%@36735 (> (Fractions 100) 0)) :lblneg @36735)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@36743 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@8@@0 |nw#_108@0| Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@8@@0 |nw#_108@0| Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@8@@0 |nw#_108@0| Node.valid) perm$N)))))) :lblneg @36743)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@8@@0 |nw#_108@0| Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@8@@0 |nw#_108@0| Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@8@@0 |nw#_108@0| Node.valid) perm$N))))) (=> (= |exhaleMask#_119@0| (MapType1Store Mask@8@@0 |nw#_108@0| Node.valid (MapType0Store (MapType1Select Mask@8@@0 |nw#_108@0| Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@8@@0 |nw#_108@0| Node.valid) perm$R)) (Fractions 100)))))) (and
anon9_Then_correct@@0
anon9_Else_correct@@0))))))))))))))))
(let ((anon8_Else_correct@@0 (=> (! (and %lbl%+8215 true) :lblpos +8215) (=> (and
(= (MapType2Select Heap@1@@1 |nw#_108@0| Node.next) null)
(= Mask@7@@0 Mask@5@@1)) anon2_correct@@4))))
(let ((anon8_Then_correct@@0 (=> (! (and %lbl%+8213 true) :lblpos +8213) (=> (not (= (MapType2Select Heap@1@@1 |nw#_108@0| Node.next) null)) (and
(! (or %lbl%@36447 (> (Fractions 100) 0)) :lblneg @36447)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@36455 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@5@@1 (MapType2Select Heap@1@@1 |nw#_108@0| Node.next) Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@5@@1 (MapType2Select Heap@1@@1 |nw#_108@0| Node.next) Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@5@@1 (MapType2Select Heap@1@@1 |nw#_108@0| Node.next) Node.valid) perm$N)))))) :lblneg @36455)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@5@@1 (MapType2Select Heap@1@@1 |nw#_108@0| Node.next) Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@5@@1 (MapType2Select Heap@1@@1 |nw#_108@0| Node.next) Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@5@@1 (MapType2Select Heap@1@@1 |nw#_108@0| Node.next) Node.valid) perm$N))))) (=> (= Mask@6@@1 (MapType1Store Mask@5@@1 (MapType2Select Heap@1@@1 |nw#_108@0| Node.next) Node.valid (MapType0Store (MapType1Select Mask@5@@1 (MapType2Select Heap@1@@1 |nw#_108@0| Node.next) Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@5@@1 (MapType2Select Heap@1@@1 |nw#_108@0| Node.next) Node.valid) perm$R)) (Fractions 100)))))) (=> (and
(wf Heap@1@@1 Mask@6@@1 ZeroMask)
(= Mask@7@@0 Mask@6@@1)) anon2_correct@@4))))))))))
(let ((anon0_correct@@5 (=> (! (and %lbl%+8211 true) :lblpos +8211) (=> (and
(< 0 |methodK#_91@@0|)
(< (* 1000 |methodK#_91@@0|) (Fractions 1))) (=> (and
(= CurrentModule |module#default|)
CanAssumeFunctionDefs
(not (= this@@13 null))
(wf Heap@@7 ZeroMask ZeroMask)
(> (Fractions 100) 0)
(= Mask@0@@4 (MapType1Store ZeroMask this@@13 Node.valid (MapType0Store (MapType1Select ZeroMask this@@13 Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select ZeroMask this@@13 Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@0@@4)
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@13 Node.valid)))
(wf Heap@@7 Mask@0@@4 ZeroMask)
(wf Heap@@7 Mask@0@@4 ZeroMask)
(IsGoodMask Mask@0@@4)
(wf Heap@@7 Mask@0@@4 ZeroMask)
(= Heap@@7 Heap@@7)
(= Mask@0@@4 Mask@@7)
(= ZeroMask SecMask@@7)
(= ZeroCredits Credits)
(not (= |nw#_108@0| null))
(= (dtype |nw#_108@0|) |Node#t|)
(forall ((f@@17 T@U) ) (! (let ((|T#_1| (FieldTypeInv0 (type f@@17))))
(=> (= (type f@@17) (FieldType |T#_1|)) (and
(= (U_2_int (MapType0Select (MapType1Select Mask@0@@4 |nw#_108@0| f@@17) perm$R)) 0)
(= (U_2_int (MapType0Select (MapType1Select Mask@0@@4 |nw#_108@0| f@@17) perm$N)) 0))))
 :qid |crashbpl.1041:24|
 :skolemid |54|
 :no-pattern (type f@@17)
 :no-pattern (U_2_int f@@17)
 :no-pattern (U_2_bool f@@17)
))
(= (MapType2Select Heap@@7 |nw#_108@0| mu) $LockBottom)
(<= (U_2_int (MapType2Select Heap@@7 |nw#_108@0| held)) 0)
(iff (U_2_bool (MapType2Select Heap@@7 |nw#_108@0| rdheld)) false)
(= Mask@1@@4 (MapType1Store Mask@0@@4 |nw#_108@0| Node.next (MapType0Store (MapType1Select Mask@0@@4 |nw#_108@0| Node.next) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@0@@4 |nw#_108@0| Node.next) perm$R)) (Fractions 100))))))
(= Mask@2@@2 (MapType1Store Mask@1@@4 |nw#_108@0| Node.value (MapType0Store (MapType1Select Mask@1@@4 |nw#_108@0| Node.value) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@1@@4 |nw#_108@0| Node.value) perm$R)) (Fractions 100))))))
(= Mask@3@@1 (MapType1Store Mask@2@@2 |nw#_108@0| mu (MapType0Store (MapType1Select Mask@2@@2 |nw#_108@0| mu) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@2@@2 |nw#_108@0| mu) perm$R)) (Fractions 100))))))) (and
(! (or %lbl%@36128 (CanWrite Mask@3@@1 |nw#_108@0| Node.value)) :lblneg @36128)
(=> (CanWrite Mask@3@@1 |nw#_108@0| Node.value) (=> (and
(= Heap@0@@4 (MapType2Store Heap@@7 |nw#_108@0| Node.value (int_2_U |x#4|)))
(wf Heap@0@@4 Mask@3@@1 ZeroMask)) (and
(! (or %lbl%@36155 (CanWrite Mask@3@@1 |nw#_108@0| Node.next)) :lblneg @36155)
(=> (CanWrite Mask@3@@1 |nw#_108@0| Node.next) (=> (= Heap@1@@1 (MapType2Store Heap@0@@4 |nw#_108@0| Node.next this@@13)) (=> (and
(wf Heap@1@@1 Mask@3@@1 ZeroMask)
(|#Node.valid#trigger| |nw#_108@0|)) (=> (and
(< 0 |foldK#_112|)
(< (* 1000 |foldK#_112|) (Fractions 1))
(< (* 1000 |foldK#_112|) |methodK#_91@@0|)) (and
(! (or %lbl%@36216 (not (= |nw#_108@0| null))) :lblneg @36216)
(=> (not (= |nw#_108@0| null)) (and
(! (or %lbl%@36221 (> (Fractions 100) 0)) :lblneg @36221)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@36229 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@3@@1 |nw#_108@0| Node.next) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@3@@1 |nw#_108@0| Node.next) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@3@@1 |nw#_108@0| Node.next) perm$N)))))) :lblneg @36229)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@3@@1 |nw#_108@0| Node.next) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@3@@1 |nw#_108@0| Node.next) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@3@@1 |nw#_108@0| Node.next) perm$N))))) (=> (and
(= Mask@4@@1 (MapType1Store Mask@3@@1 |nw#_108@0| Node.next (MapType0Store (MapType1Select Mask@3@@1 |nw#_108@0| Node.next) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@3@@1 |nw#_108@0| Node.next) perm$R)) (Fractions 100))))))
(wf Heap@1@@1 Mask@4@@1 ZeroMask)) (and
(! (or %lbl%@36323 (> (Fractions 100) 0)) :lblneg @36323)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@36331 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@4@@1 |nw#_108@0| Node.value) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@4@@1 |nw#_108@0| Node.value) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@4@@1 |nw#_108@0| Node.value) perm$N)))))) :lblneg @36331)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@4@@1 |nw#_108@0| Node.value) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@4@@1 |nw#_108@0| Node.value) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@4@@1 |nw#_108@0| Node.value) perm$N))))) (=> (and
(= Mask@5@@1 (MapType1Store Mask@4@@1 |nw#_108@0| Node.value (MapType0Store (MapType1Select Mask@4@@1 |nw#_108@0| Node.value) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@4@@1 |nw#_108@0| Node.value) perm$R)) (Fractions 100))))))
(wf Heap@1@@1 Mask@5@@1 ZeroMask)) (and
anon8_Then_correct@@0
anon8_Else_correct@@0))))))))))))))))))))))))))
(let ((PreconditionGeneratedEntry_correct@@5 (=> (! (and %lbl%+35624 true) :lblpos +35624) (=> (IsGoodMask Mask@@7) (=> (and
(IsGoodMask SecMask@@7)
(or
(= this@@13 null)
(= (dtype this@@13) |Node#t|))) (=> (and
(or
(= |rt#5@@0| null)
(= (dtype |rt#5@@0|) |Node#t|))
(or
(= |n#7| null)
(= (dtype |n#7|) |Node#t|))
(not (= this@@13 null))
(wf Heap@@7 Mask@@7 SecMask@@7)) anon0_correct@@5))))))
PreconditionGeneratedEntry_correct@@5)))))))))))))
))
(check-sat)
(pop 1)
(declare-fun this@@14 () T@U)
(declare-fun |unfoldingMask#_123@4| () T@U)
(declare-fun |unfoldingHeap#_122@1| () T@U)
(declare-fun |exhaleMask#_144@0| () T@U)
(declare-fun |exhaleHeap#_143@0| () T@U)
(declare-fun Mask@0@@5 () T@U)
(declare-fun SecMask@2 () T@U)
(declare-fun SecMask@3 () T@U)
(declare-fun SecMask@1 () T@U)
(declare-fun |unfoldingMask#_123@2| () T@U)
(declare-fun |unfoldingMask#_123@3| () T@U)
(declare-fun |unfoldingMask#_123@0| () T@U)
(declare-fun |unfoldingMask#_123@1| () T@U)
(declare-fun |unfoldingHeap#_122@0| () T@U)
(declare-fun |exhaleMask#_153@0| () T@U)
(declare-fun |exhaleHeap#_152@4| () T@U)
(declare-fun |exhaleHeap#_152@3| () T@U)
(declare-fun |exhaleHeap#_152@2| () T@U)
(declare-fun |exhaleHeap#_152@1| () T@U)
(declare-fun |exhaleHeap#_152@0| () T@U)
(declare-fun %lbl%+9896 () Bool)
(declare-fun %lbl%+9894 () Bool)
(declare-fun %lbl%+9892 () Bool)
(declare-fun %lbl%+9890 () Bool)
(declare-fun %lbl%+9888 () Bool)
(declare-fun |i#8@@3| () Int)
(declare-fun %lbl%@39158 () Bool)
(declare-fun %lbl%@39168 () Bool)
(declare-fun %lbl%@39180 () Bool)
(declare-fun |funcappK#_142| () Int)
(declare-fun %lbl%@39235 () Bool)
(declare-fun %lbl%@39245 () Bool)
(declare-fun %lbl%@39263 () Bool)
(declare-fun %lbl%@39271 () Bool)
(declare-fun %lbl%+9884 () Bool)
(declare-fun %lbl%@39130 () Bool)
(declare-fun %lbl%@39140 () Bool)
(declare-fun %lbl%+9882 () Bool)
(declare-fun %lbl%+9877 () Bool)
(declare-fun %lbl%+9875 () Bool)
(declare-fun %lbl%+9873 () Bool)
(declare-fun %lbl%+9869 () Bool)
(declare-fun %lbl%+9835 () Bool)
(declare-fun %lbl%+9830 () Bool)
(declare-fun %lbl%+9825 () Bool)
(declare-fun %lbl%+9823 () Bool)
(declare-fun %lbl%+9821 () Bool)
(declare-fun %lbl%+9817 () Bool)
(declare-fun %lbl%+9815 () Bool)
(declare-fun |oldVers#_131@0| () Int)
(declare-fun |newVers#_132@0| () Int)
(declare-fun %lbl%+9813 () Bool)
(declare-fun |unfoldingK#_127| () Int)
(declare-fun %lbl%@38166 () Bool)
(declare-fun %lbl%@38190 () Bool)
(declare-fun %lbl%@38198 () Bool)
(declare-fun %lbl%+9809 () Bool)
(declare-fun %lbl%+9807 () Bool)
(declare-fun %lbl%+9805 () Bool)
(declare-fun %lbl%+9803 () Bool)
(declare-fun %lbl%+9799 () Bool)
(declare-fun %lbl%+9794 () Bool)
(declare-fun %lbl%+9792 () Bool)
(declare-fun %lbl%+9790 () Bool)
(declare-fun |functionK#_146| () Int)
(declare-fun %lbl%@37672 () Bool)
(declare-fun %lbl%@37773 () Bool)
(declare-fun |funcappK#_151| () Int)
(declare-fun %lbl%@37824 () Bool)
(declare-fun %lbl%@37832 () Bool)
(declare-fun %lbl%+37496 () Bool)
(assert (and
(= (type this@@14) refType)
(= (type |unfoldingMask#_123@4|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |unfoldingHeap#_122@1|) (MapType2Type refType))
(= (type |exhaleMask#_144@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |exhaleHeap#_143@0|) (MapType2Type refType))
(= (type Mask@0@@5) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type SecMask@2) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type SecMask@3) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type SecMask@1) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |unfoldingMask#_123@2|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |unfoldingMask#_123@3|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |unfoldingMask#_123@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |unfoldingMask#_123@1|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |unfoldingHeap#_122@0|) (MapType2Type refType))
(= (type |exhaleMask#_153@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |exhaleHeap#_152@4|) (MapType2Type refType))
(= (type |exhaleHeap#_152@3|) (MapType2Type refType))
(= (type |exhaleHeap#_152@2|) (MapType2Type refType))
(= (type |exhaleHeap#_152@1|) (MapType2Type refType))
(= (type |exhaleHeap#_152@0|) (MapType2Type refType))))
(push 1)
(set-info :boogie-vc-id Node.at$checkDefinedness)
(assert (not
(let ((anon26_correct (=> (! (and %lbl%+9896 true) :lblpos +9896) true)))
(let ((anon25_correct (=> (! (and %lbl%+9894 true) :lblpos +9894) (=> (wf |unfoldingHeap#_122@1| |exhaleMask#_144@0| ZeroMask) (=> (and
(wf |unfoldingHeap#_122@1| |unfoldingMask#_123@4| ZeroMask)
(IsGoodExhaleState |exhaleHeap#_143@0| |unfoldingHeap#_122@1| |exhaleMask#_144@0| ZeroMask)
(IsGoodMask |exhaleMask#_144@0|)
(wf |exhaleHeap#_143@0| |exhaleMask#_144@0| ZeroMask)) anon26_correct)))))
(let ((anon39_Else_correct (=> (! (and %lbl%+9892 true) :lblpos +9892) (=> (CanRead |exhaleMask#_144@0| ZeroMask (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid) anon25_correct))))
(let ((anon39_Then_correct (=> (! (and %lbl%+9890 true) :lblpos +9890) (=> (and
(not (CanRead |exhaleMask#_144@0| ZeroMask (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid))
(< (U_2_int (MapType2Select |unfoldingHeap#_122@1| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid)) (U_2_int (MapType2Select |exhaleHeap#_143@0| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid)))) anon25_correct))))
(let ((anon38_Else_correct (=> (! (and %lbl%+9888 true) :lblpos +9888) (=> (not (= |i#8@@3| 0)) (and
(! (or %lbl%@39158 (=> true (not (= this@@14 null)))) :lblneg @39158)
(=> (=> true (not (= this@@14 null))) (and
(! (or %lbl%@39168 (=> true (CanRead |unfoldingMask#_123@4| ZeroMask this@@14 Node.next))) :lblneg @39168)
(=> (=> true (CanRead |unfoldingMask#_123@4| ZeroMask this@@14 Node.next)) (and
(! (or %lbl%@39180 (=> true (not (= (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) null)))) :lblneg @39180)
(=> (=> true (not (= (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) null))) (=> (and
(< 0 |funcappK#_142|)
(< (* 1000 |funcappK#_142|) (Fractions 1))
(wf |unfoldingHeap#_122@1| |unfoldingMask#_123@4| ZeroMask)) (and
(! (or %lbl%@39235 (<= 0 (- |i#8@@3| 1))) :lblneg @39235)
(=> (<= 0 (- |i#8@@3| 1)) (and
(! (or %lbl%@39245 (< (- |i#8@@3| 1) (|#Node.size| |unfoldingHeap#_122@1| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next)))) :lblneg @39245)
(=> (< (- |i#8@@3| 1) (|#Node.size| |unfoldingHeap#_122@1| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next))) (and
(! (or %lbl%@39263 (> (Fractions 100) 0)) :lblneg @39263)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@39271 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_123@4| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_123@4| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_123@4| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid) perm$N)))))) :lblneg @39271)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_123@4| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_123@4| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_123@4| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid) perm$N))))) (=> (= |exhaleMask#_144@0| (MapType1Store |unfoldingMask#_123@4| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid (MapType0Store (MapType1Select |unfoldingMask#_123@4| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_123@4| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid) perm$R)) (Fractions 100)))))) (and
anon39_Then_correct
anon39_Else_correct)))))))))))))))))))))
(let ((anon38_Then_correct (=> (! (and %lbl%+9884 true) :lblpos +9884) (=> (= |i#8@@3| 0) (and
(! (or %lbl%@39130 (=> true (not (= this@@14 null)))) :lblneg @39130)
(=> (=> true (not (= this@@14 null))) (and
(! (or %lbl%@39140 (=> true (CanRead |unfoldingMask#_123@4| ZeroMask this@@14 Node.value))) :lblneg @39140)
(=> (=> true (CanRead |unfoldingMask#_123@4| ZeroMask this@@14 Node.value)) anon26_correct))))))))
(let ((anon21_correct (=> (! (and %lbl%+9882 true) :lblpos +9882) (and
anon38_Then_correct
anon38_Else_correct))))
(let ((anon37_Else_correct (=> (! (and %lbl%+9877 true) :lblpos +9877) (=> (= (MapType2Select Heap@@7 this@@14 Node.next) null) anon21_correct))))
(let ((anon37_Then_correct (=> (! (and %lbl%+9875 true) :lblpos +9875) (=> (not (= (MapType2Select Heap@@7 this@@14 Node.next) null)) (=> (and
(not (= (MapType2Select Heap@@7 this@@14 Node.next) null))
(wf Heap@@7 Mask@0@@5 SecMask@2)
(> (Fractions 100) 0)
(= SecMask@3 (MapType1Store SecMask@2 (MapType2Select Heap@@7 this@@14 Node.next) Node.valid (MapType0Store (MapType1Select SecMask@2 (MapType2Select Heap@@7 this@@14 Node.next) Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select SecMask@2 (MapType2Select Heap@@7 this@@14 Node.next) Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@0@@5)
(IsGoodState (heapFragment (MapType2Select Heap@@7 (MapType2Select Heap@@7 this@@14 Node.next) Node.valid)))
(wf Heap@@7 Mask@0@@5 SecMask@3)
(wf Heap@@7 Mask@0@@5 SecMask@3)) (and
anon38_Then_correct
anon38_Else_correct))))))
(let ((anon19_correct (=> (! (and %lbl%+9873 true) :lblpos +9873) (=> (not (= this@@14 null)) (=> (and
(wf Heap@@7 Mask@0@@5 ZeroMask)
(or
(= (MapType2Select Heap@@7 this@@14 Node.next) null)
(= (dtype (MapType2Select Heap@@7 this@@14 Node.next)) |Node#t|))
(> (Fractions 100) 0)
(= SecMask@1 (MapType1Store ZeroMask this@@14 Node.next (MapType0Store (MapType1Select ZeroMask this@@14 Node.next) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select ZeroMask this@@14 Node.next) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@0@@5)
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@14 Node.next)))
(wf Heap@@7 Mask@0@@5 SecMask@1)
(wf Heap@@7 Mask@0@@5 SecMask@1)
(not (= this@@14 null))
(wf Heap@@7 Mask@0@@5 SecMask@1)
(> (Fractions 100) 0)
(= SecMask@2 (MapType1Store SecMask@1 this@@14 Node.value (MapType0Store (MapType1Select SecMask@1 this@@14 Node.value) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select SecMask@1 this@@14 Node.value) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@0@@5)
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@14 Node.value)))
(wf Heap@@7 Mask@0@@5 SecMask@2)
(wf Heap@@7 Mask@0@@5 SecMask@2)) (and
anon37_Then_correct
anon37_Else_correct))))))
(let ((anon32_Else_correct (=> (! (and %lbl%+9869 true) :lblpos +9869) (=> (not false) anon19_correct))))
(let ((anon32_Then_correct (=> (! (and %lbl%+9835 true) :lblpos +9835) true)))
(let ((anon9_correct@@0 (=> (! (and %lbl%+9830 true) :lblpos +9830) (=> (and
(IsGoodMask |unfoldingMask#_123@4|)
(wf |unfoldingHeap#_122@1| |unfoldingMask#_123@4| ZeroMask)) (and
anon32_Then_correct
anon32_Else_correct)))))
(let ((anon31_Else_correct (=> (! (and %lbl%+9825 true) :lblpos +9825) (=> (and
(= (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) null)
(= |unfoldingMask#_123@4| |unfoldingMask#_123@2|)) anon9_correct@@0))))
(let ((anon31_Then_correct (=> (! (and %lbl%+9823 true) :lblpos +9823) (=> (and
(not (= (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) null))
(not (= (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) null))) (=> (and
(wf |unfoldingHeap#_122@1| |unfoldingMask#_123@2| ZeroMask)
(> (Fractions 100) 0)
(= |unfoldingMask#_123@3| (MapType1Store |unfoldingMask#_123@2| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid (MapType0Store (MapType1Select |unfoldingMask#_123@2| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_123@2| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask |unfoldingMask#_123@3|)
(IsGoodState (heapFragment (MapType2Select |unfoldingHeap#_122@1| (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) Node.valid)))
(wf |unfoldingHeap#_122@1| |unfoldingMask#_123@3| ZeroMask)
(wf |unfoldingHeap#_122@1| |unfoldingMask#_123@3| ZeroMask)
(= |unfoldingMask#_123@4| |unfoldingMask#_123@3|)) anon9_correct@@0)))))
(let ((anon7_correct@@1 (=> (! (and %lbl%+9821 true) :lblpos +9821) (=> (and
(wf |unfoldingHeap#_122@1| |unfoldingMask#_123@0| ZeroMask)
(IsGoodMask |unfoldingMask#_123@0|)
(wf |unfoldingHeap#_122@1| |unfoldingMask#_123@0| ZeroMask)
(not (= this@@14 null))) (=> (and
(wf |unfoldingHeap#_122@1| |unfoldingMask#_123@0| ZeroMask)
(or
(= (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next) null)
(= (dtype (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next)) |Node#t|))
(> (Fractions 100) 0)
(= |unfoldingMask#_123@1| (MapType1Store |unfoldingMask#_123@0| this@@14 Node.next (MapType0Store (MapType1Select |unfoldingMask#_123@0| this@@14 Node.next) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_123@0| this@@14 Node.next) perm$R)) (Fractions 100))))))
(IsGoodMask |unfoldingMask#_123@1|)
(IsGoodState (heapFragment (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.next)))
(wf |unfoldingHeap#_122@1| |unfoldingMask#_123@1| ZeroMask)
(wf |unfoldingHeap#_122@1| |unfoldingMask#_123@1| ZeroMask)
(not (= this@@14 null))
(wf |unfoldingHeap#_122@1| |unfoldingMask#_123@1| ZeroMask)
(> (Fractions 100) 0)
(= |unfoldingMask#_123@2| (MapType1Store |unfoldingMask#_123@1| this@@14 Node.value (MapType0Store (MapType1Select |unfoldingMask#_123@1| this@@14 Node.value) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_123@1| this@@14 Node.value) perm$R)) (Fractions 100))))))
(IsGoodMask |unfoldingMask#_123@2|)
(IsGoodState (heapFragment (MapType2Select |unfoldingHeap#_122@1| this@@14 Node.value)))
(wf |unfoldingHeap#_122@1| |unfoldingMask#_123@2| ZeroMask)
(wf |unfoldingHeap#_122@1| |unfoldingMask#_123@2| ZeroMask)) (and
anon31_Then_correct
anon31_Else_correct))))))
(let ((anon30_Else_correct (=> (! (and %lbl%+9817 true) :lblpos +9817) (=> (and
(CanRead |unfoldingMask#_123@0| ZeroMask this@@14 Node.valid)
(= |unfoldingHeap#_122@1| Heap@@7)) anon7_correct@@1))))
(let ((anon30_Then_correct (=> (! (and %lbl%+9815 true) :lblpos +9815) (=> (not (CanRead |unfoldingMask#_123@0| ZeroMask this@@14 Node.valid)) (=> (and
(= |oldVers#_131@0| (U_2_int (MapType2Select Heap@@7 this@@14 Node.valid)))
(= |unfoldingHeap#_122@0| (MapType2Store Heap@@7 this@@14 Node.valid (int_2_U |newVers#_132@0|)))
(< |oldVers#_131@0| (U_2_int (MapType2Select |unfoldingHeap#_122@0| this@@14 Node.valid)))
(= |unfoldingHeap#_122@1| |unfoldingHeap#_122@0|)) anon7_correct@@1)))))
(let ((anon5_correct (=> (! (and %lbl%+9813 true) :lblpos +9813) (=> (and
(IsGoodMask |exhaleMask#_153@0|)
(wf |exhaleHeap#_152@4| |exhaleMask#_153@0| ZeroMask)
(< |i#8@@3| (|#Node.size| Heap@@7 this@@14))
(IsGoodMask Mask@0@@5)
(wf Heap@@7 Mask@0@@5 ZeroMask)
(= CurrentModule |module#default|)
(< 0 |unfoldingK#_127|)
(< (* 1000 |unfoldingK#_127|) (Fractions 1))) (and
(! (or %lbl%@38166 (=> true (not (= this@@14 null)))) :lblneg @38166)
(=> (=> true (not (= this@@14 null))) (=> (wf Heap@@7 Mask@0@@5 ZeroMask) (and
(! (or %lbl%@38190 (> (Fractions 100) 0)) :lblneg @38190)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@38198 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$N)))))) :lblneg @38198)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$N))))) (=> (= |unfoldingMask#_123@0| (MapType1Store Mask@0@@5 this@@14 Node.valid (MapType0Store (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$R)) (Fractions 100)))))) (and
anon30_Then_correct
anon30_Else_correct)))))))))))))
(let ((anon28_Else_correct (=> (! (and %lbl%+9809 true) :lblpos +9809) (=> (and
(not (CanRead |exhaleMask#_153@0| ZeroMask this@@14 Node.valid))
(= |exhaleHeap#_152@4| |exhaleHeap#_152@0|)) anon5_correct))))
(let ((anon29_Else_correct (=> (! (and %lbl%+9807 true) :lblpos +9807) (=> (and
(= (MapType2Select Heap@@7 this@@14 Node.next) null)
(= |exhaleHeap#_152@4| |exhaleHeap#_152@2|)) anon5_correct))))
(let ((anon29_Then_correct (=> (! (and %lbl%+9805 true) :lblpos +9805) (=> (not (= (MapType2Select Heap@@7 this@@14 Node.next) null)) (=> (and
(= |exhaleHeap#_152@3| (MapType2Store |exhaleHeap#_152@2| (MapType2Select Heap@@7 this@@14 Node.next) Node.valid (MapType2Select Heap@@7 (MapType2Select Heap@@7 this@@14 Node.next) Node.valid)))
(= |exhaleHeap#_152@4| |exhaleHeap#_152@3|)) anon5_correct)))))
(let ((anon28_Then_correct (=> (! (and %lbl%+9803 true) :lblpos +9803) (=> (CanRead |exhaleMask#_153@0| ZeroMask this@@14 Node.valid) (=> (and
(= |exhaleHeap#_152@1| (MapType2Store |exhaleHeap#_152@0| this@@14 Node.next (MapType2Select Heap@@7 this@@14 Node.next)))
(= |exhaleHeap#_152@2| (MapType2Store |exhaleHeap#_152@1| this@@14 Node.value (MapType2Select Heap@@7 this@@14 Node.value)))) (and
anon29_Then_correct
anon29_Else_correct))))))
(let ((anon2_correct@@5 (=> (! (and %lbl%+9799 true) :lblpos +9799) (=> (wf Heap@@7 |exhaleMask#_153@0| ZeroMask) (=> (and
(wf Heap@@7 Mask@0@@5 ZeroMask)
(IsGoodExhaleState |exhaleHeap#_152@0| Heap@@7 |exhaleMask#_153@0| ZeroMask)) (and
anon28_Then_correct
anon28_Else_correct))))))
(let ((anon27_Else_correct (=> (! (and %lbl%+9794 true) :lblpos +9794) (=> (CanRead |exhaleMask#_153@0| ZeroMask this@@14 Node.valid) anon2_correct@@5))))
(let ((anon27_Then_correct (=> (! (and %lbl%+9792 true) :lblpos +9792) (=> (and
(not (CanRead |exhaleMask#_153@0| ZeroMask this@@14 Node.valid))
(< (U_2_int (MapType2Select Heap@@7 this@@14 Node.valid)) (U_2_int (MapType2Select |exhaleHeap#_152@0| this@@14 Node.valid)))) anon2_correct@@5))))
(let ((anon0_correct@@6 (=> (! (and %lbl%+9790 true) :lblpos +9790) (=> (and
(< 0 |functionK#_146|)
(< (* 1000 |functionK#_146|) (Fractions 1))) (and
(! (or %lbl%@37672 (not (= this@@14 null))) :lblneg @37672)
(=> (not (= this@@14 null)) (=> (not (= this@@14 null)) (=> (and
(wf Heap@@7 ZeroMask ZeroMask)
(> (Fractions 100) 0)
(= Mask@0@@5 (MapType1Store ZeroMask this@@14 Node.valid (MapType0Store (MapType1Select ZeroMask this@@14 Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select ZeroMask this@@14 Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@0@@5)
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@14 Node.valid)))
(wf Heap@@7 Mask@0@@5 ZeroMask)
(wf Heap@@7 Mask@0@@5 ZeroMask)
(<= 0 |i#8@@3|)) (and
(! (or %lbl%@37773 (=> true (not (= this@@14 null)))) :lblneg @37773)
(=> (=> true (not (= this@@14 null))) (=> (and
(< 0 |funcappK#_151|)
(< (* 1000 |funcappK#_151|) (Fractions 1))
(wf Heap@@7 Mask@0@@5 ZeroMask)) (and
(! (or %lbl%@37824 (> (Fractions 100) 0)) :lblneg @37824)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@37832 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$N)))))) :lblneg @37832)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$N))))) (=> (= |exhaleMask#_153@0| (MapType1Store Mask@0@@5 this@@14 Node.valid (MapType0Store (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@0@@5 this@@14 Node.valid) perm$R)) (Fractions 100)))))) (and
anon27_Then_correct
anon27_Else_correct)))))))))))))))))
(let ((PreconditionGeneratedEntry_correct@@6 (=> (! (and %lbl%+37496 true) :lblpos +37496) (=> (IsGoodMask Mask@@7) (=> (and
(IsGoodMask SecMask@@7)
(or
(= this@@14 null)
(= (dtype this@@14) |Node#t|))
(not (= this@@14 null))
(wf Heap@@7 Mask@@7 SecMask@@7)) anon0_correct@@6)))))
PreconditionGeneratedEntry_correct@@6))))))))))))))))))))))))))))
))
(check-sat)
;; (get-info :reason-unknown)
;; (labels)
(assert %lbl%@39245)
(check-sat)
(pop 1)
(declare-fun |unfoldingHeap#_155@1| () T@U)
(declare-fun |exhaleMask#_177@0| () T@U)
(declare-fun |unfoldingMask#_156@4| () T@U)
(declare-fun |exhaleHeap#_176@0| () T@U)
(declare-fun this@@15 () T@U)
(declare-fun Mask@0@@6 () T@U)
(declare-fun SecMask@2@@0 () T@U)
(declare-fun SecMask@3@@0 () T@U)
(declare-fun SecMask@1@@0 () T@U)
(declare-fun |unfoldingMask#_156@2| () T@U)
(declare-fun |unfoldingMask#_156@3| () T@U)
(declare-fun |unfoldingMask#_156@0| () T@U)
(declare-fun |unfoldingMask#_156@1| () T@U)
(declare-fun |unfoldingHeap#_155@0| () T@U)
(declare-fun %lbl%+11558 () Bool)
(declare-fun %lbl%+11556 () Bool)
(declare-fun %lbl%+11554 () Bool)
(declare-fun %lbl%+11552 () Bool)
(declare-fun %lbl%+11550 () Bool)
(declare-fun %lbl%+11548 () Bool)
(declare-fun %lbl%@41216 () Bool)
(declare-fun %lbl%@41226 () Bool)
(declare-fun %lbl%@41238 () Bool)
(declare-fun |funcappK#_175| () Int)
(declare-fun %lbl%@41293 () Bool)
(declare-fun %lbl%@41301 () Bool)
(declare-fun %lbl%+11544 () Bool)
(declare-fun %lbl%@41181 () Bool)
(declare-fun %lbl%@41191 () Bool)
(declare-fun %lbl%+11540 () Bool)
(declare-fun %lbl%+11538 () Bool)
(declare-fun %lbl%+11536 () Bool)
(declare-fun %lbl%+11532 () Bool)
(declare-fun %lbl%+11498 () Bool)
(declare-fun %lbl%+11493 () Bool)
(declare-fun %lbl%+11488 () Bool)
(declare-fun %lbl%+11486 () Bool)
(declare-fun %lbl%+11484 () Bool)
(declare-fun %lbl%+11480 () Bool)
(declare-fun %lbl%+11478 () Bool)
(declare-fun |oldVers#_164@0| () Int)
(declare-fun |newVers#_165@0| () Int)
(declare-fun %lbl%+11476 () Bool)
(declare-fun |functionK#_179| () Int)
(declare-fun %lbl%@40090 () Bool)
(declare-fun |unfoldingK#_160| () Int)
(declare-fun %lbl%@40223 () Bool)
(declare-fun %lbl%@40247 () Bool)
(declare-fun %lbl%@40255 () Bool)
(declare-fun %lbl%+39942 () Bool)
(assert (and
(= (type |unfoldingHeap#_155@1|) (MapType2Type refType))
(= (type |exhaleMask#_177@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |unfoldingMask#_156@4|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |exhaleHeap#_176@0|) (MapType2Type refType))
(= (type this@@15) refType)
(= (type Mask@0@@6) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type SecMask@2@@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type SecMask@3@@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type SecMask@1@@0) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |unfoldingMask#_156@2|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |unfoldingMask#_156@3|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |unfoldingMask#_156@0|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |unfoldingMask#_156@1|) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type |unfoldingHeap#_155@0|) (MapType2Type refType))))
(push 1)
(set-info :boogie-vc-id Node.size$checkDefinedness)
(assert (not
(let ((anon20_correct (=> (! (and %lbl%+11558 true) :lblpos +11558) true)))
(let ((anon29_Else_correct@@0 (=> (! (and %lbl%+11556 true) :lblpos +11556) (=> (= (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) null) anon20_correct))))
(let ((anon19_correct@@0 (=> (! (and %lbl%+11554 true) :lblpos +11554) (=> (wf |unfoldingHeap#_155@1| |exhaleMask#_177@0| ZeroMask) (=> (and
(wf |unfoldingHeap#_155@1| |unfoldingMask#_156@4| ZeroMask)
(IsGoodExhaleState |exhaleHeap#_176@0| |unfoldingHeap#_155@1| |exhaleMask#_177@0| ZeroMask)
(IsGoodMask |exhaleMask#_177@0|)
(wf |exhaleHeap#_176@0| |exhaleMask#_177@0| ZeroMask)) anon20_correct)))))
(let ((anon30_Else_correct@@0 (=> (! (and %lbl%+11552 true) :lblpos +11552) (=> (CanRead |exhaleMask#_177@0| ZeroMask (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid) anon19_correct@@0))))
(let ((anon30_Then_correct@@0 (=> (! (and %lbl%+11550 true) :lblpos +11550) (=> (and
(not (CanRead |exhaleMask#_177@0| ZeroMask (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid))
(< (U_2_int (MapType2Select |unfoldingHeap#_155@1| (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid)) (U_2_int (MapType2Select |exhaleHeap#_176@0| (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid)))) anon19_correct@@0))))
(let ((anon29_Then_correct@@0 (=> (! (and %lbl%+11548 true) :lblpos +11548) (=> (not (= (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) null)) (and
(! (or %lbl%@41216 (=> true (not (= this@@15 null)))) :lblneg @41216)
(=> (=> true (not (= this@@15 null))) (and
(! (or %lbl%@41226 (=> true (CanRead |unfoldingMask#_156@4| ZeroMask this@@15 Node.next))) :lblneg @41226)
(=> (=> true (CanRead |unfoldingMask#_156@4| ZeroMask this@@15 Node.next)) (and
(! (or %lbl%@41238 (=> true (not (= (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) null)))) :lblneg @41238)
(=> (=> true (not (= (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) null))) (=> (and
(< 0 |funcappK#_175|)
(< (* 1000 |funcappK#_175|) (Fractions 1))
(wf |unfoldingHeap#_155@1| |unfoldingMask#_156@4| ZeroMask)) (and
(! (or %lbl%@41293 (> (Fractions 100) 0)) :lblneg @41293)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@41301 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_156@4| (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_156@4| (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_156@4| (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid) perm$N)))))) :lblneg @41301)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_156@4| (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_156@4| (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_156@4| (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid) perm$N))))) (=> (= |exhaleMask#_177@0| (MapType1Store |unfoldingMask#_156@4| (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid (MapType0Store (MapType1Select |unfoldingMask#_156@4| (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_156@4| (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid) perm$R)) (Fractions 100)))))) (and
anon30_Then_correct@@0
anon30_Else_correct@@0)))))))))))))))))
(let ((anon16_correct@@0 (=> (! (and %lbl%+11544 true) :lblpos +11544) (and
(! (or %lbl%@41181 (=> true (not (= this@@15 null)))) :lblneg @41181)
(=> (=> true (not (= this@@15 null))) (and
(! (or %lbl%@41191 (=> true (CanRead |unfoldingMask#_156@4| ZeroMask this@@15 Node.next))) :lblneg @41191)
(=> (=> true (CanRead |unfoldingMask#_156@4| ZeroMask this@@15 Node.next)) (and
anon29_Then_correct@@0
anon29_Else_correct@@0))))))))
(let ((anon28_Else_correct@@0 (=> (! (and %lbl%+11540 true) :lblpos +11540) (=> (= (MapType2Select Heap@@7 this@@15 Node.next) null) anon16_correct@@0))))
(let ((anon28_Then_correct@@0 (=> (! (and %lbl%+11538 true) :lblpos +11538) (=> (not (= (MapType2Select Heap@@7 this@@15 Node.next) null)) (=> (and
(not (= (MapType2Select Heap@@7 this@@15 Node.next) null))
(wf Heap@@7 Mask@0@@6 SecMask@2@@0)
(> (Fractions 100) 0)
(= SecMask@3@@0 (MapType1Store SecMask@2@@0 (MapType2Select Heap@@7 this@@15 Node.next) Node.valid (MapType0Store (MapType1Select SecMask@2@@0 (MapType2Select Heap@@7 this@@15 Node.next) Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select SecMask@2@@0 (MapType2Select Heap@@7 this@@15 Node.next) Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@0@@6)
(IsGoodState (heapFragment (MapType2Select Heap@@7 (MapType2Select Heap@@7 this@@15 Node.next) Node.valid)))
(wf Heap@@7 Mask@0@@6 SecMask@3@@0)
(wf Heap@@7 Mask@0@@6 SecMask@3@@0)) anon16_correct@@0)))))
(let ((anon14_correct (=> (! (and %lbl%+11536 true) :lblpos +11536) (=> (not (= this@@15 null)) (=> (and
(wf Heap@@7 Mask@0@@6 ZeroMask)
(or
(= (MapType2Select Heap@@7 this@@15 Node.next) null)
(= (dtype (MapType2Select Heap@@7 this@@15 Node.next)) |Node#t|))
(> (Fractions 100) 0)
(= SecMask@1@@0 (MapType1Store ZeroMask this@@15 Node.next (MapType0Store (MapType1Select ZeroMask this@@15 Node.next) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select ZeroMask this@@15 Node.next) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@0@@6)
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@15 Node.next)))
(wf Heap@@7 Mask@0@@6 SecMask@1@@0)
(wf Heap@@7 Mask@0@@6 SecMask@1@@0)
(not (= this@@15 null))
(wf Heap@@7 Mask@0@@6 SecMask@1@@0)
(> (Fractions 100) 0)
(= SecMask@2@@0 (MapType1Store SecMask@1@@0 this@@15 Node.value (MapType0Store (MapType1Select SecMask@1@@0 this@@15 Node.value) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select SecMask@1@@0 this@@15 Node.value) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@0@@6)
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@15 Node.value)))
(wf Heap@@7 Mask@0@@6 SecMask@2@@0)
(wf Heap@@7 Mask@0@@6 SecMask@2@@0)) (and
anon28_Then_correct@@0
anon28_Else_correct@@0))))))
(let ((anon23_Else_correct@@0 (=> (! (and %lbl%+11532 true) :lblpos +11532) (=> (not false) anon14_correct))))
(let ((anon23_Then_correct@@0 (=> (! (and %lbl%+11498 true) :lblpos +11498) true)))
(let ((anon4_correct@@4 (=> (! (and %lbl%+11493 true) :lblpos +11493) (=> (and
(IsGoodMask |unfoldingMask#_156@4|)
(wf |unfoldingHeap#_155@1| |unfoldingMask#_156@4| ZeroMask)) (and
anon23_Then_correct@@0
anon23_Else_correct@@0)))))
(let ((anon22_Else_correct@@0 (=> (! (and %lbl%+11488 true) :lblpos +11488) (=> (and
(= (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) null)
(= |unfoldingMask#_156@4| |unfoldingMask#_156@2|)) anon4_correct@@4))))
(let ((anon22_Then_correct@@0 (=> (! (and %lbl%+11486 true) :lblpos +11486) (=> (and
(not (= (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) null))
(not (= (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) null))) (=> (and
(wf |unfoldingHeap#_155@1| |unfoldingMask#_156@2| ZeroMask)
(> (Fractions 100) 0)
(= |unfoldingMask#_156@3| (MapType1Store |unfoldingMask#_156@2| (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid (MapType0Store (MapType1Select |unfoldingMask#_156@2| (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_156@2| (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask |unfoldingMask#_156@3|)
(IsGoodState (heapFragment (MapType2Select |unfoldingHeap#_155@1| (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) Node.valid)))
(wf |unfoldingHeap#_155@1| |unfoldingMask#_156@3| ZeroMask)
(wf |unfoldingHeap#_155@1| |unfoldingMask#_156@3| ZeroMask)
(= |unfoldingMask#_156@4| |unfoldingMask#_156@3|)) anon4_correct@@4)))))
(let ((anon2_correct@@6 (=> (! (and %lbl%+11484 true) :lblpos +11484) (=> (and
(wf |unfoldingHeap#_155@1| |unfoldingMask#_156@0| ZeroMask)
(IsGoodMask |unfoldingMask#_156@0|)
(wf |unfoldingHeap#_155@1| |unfoldingMask#_156@0| ZeroMask)
(not (= this@@15 null))) (=> (and
(wf |unfoldingHeap#_155@1| |unfoldingMask#_156@0| ZeroMask)
(or
(= (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next) null)
(= (dtype (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next)) |Node#t|))
(> (Fractions 100) 0)
(= |unfoldingMask#_156@1| (MapType1Store |unfoldingMask#_156@0| this@@15 Node.next (MapType0Store (MapType1Select |unfoldingMask#_156@0| this@@15 Node.next) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_156@0| this@@15 Node.next) perm$R)) (Fractions 100))))))
(IsGoodMask |unfoldingMask#_156@1|)
(IsGoodState (heapFragment (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.next)))
(wf |unfoldingHeap#_155@1| |unfoldingMask#_156@1| ZeroMask)
(wf |unfoldingHeap#_155@1| |unfoldingMask#_156@1| ZeroMask)
(not (= this@@15 null))
(wf |unfoldingHeap#_155@1| |unfoldingMask#_156@1| ZeroMask)
(> (Fractions 100) 0)
(= |unfoldingMask#_156@2| (MapType1Store |unfoldingMask#_156@1| this@@15 Node.value (MapType0Store (MapType1Select |unfoldingMask#_156@1| this@@15 Node.value) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select |unfoldingMask#_156@1| this@@15 Node.value) perm$R)) (Fractions 100))))))
(IsGoodMask |unfoldingMask#_156@2|)
(IsGoodState (heapFragment (MapType2Select |unfoldingHeap#_155@1| this@@15 Node.value)))
(wf |unfoldingHeap#_155@1| |unfoldingMask#_156@2| ZeroMask)
(wf |unfoldingHeap#_155@1| |unfoldingMask#_156@2| ZeroMask)) (and
anon22_Then_correct@@0
anon22_Else_correct@@0))))))
(let ((anon21_Else_correct@@0 (=> (! (and %lbl%+11480 true) :lblpos +11480) (=> (and
(CanRead |unfoldingMask#_156@0| ZeroMask this@@15 Node.valid)
(= |unfoldingHeap#_155@1| Heap@@7)) anon2_correct@@6))))
(let ((anon21_Then_correct@@0 (=> (! (and %lbl%+11478 true) :lblpos +11478) (=> (not (CanRead |unfoldingMask#_156@0| ZeroMask this@@15 Node.valid)) (=> (and
(= |oldVers#_164@0| (U_2_int (MapType2Select Heap@@7 this@@15 Node.valid)))
(= |unfoldingHeap#_155@0| (MapType2Store Heap@@7 this@@15 Node.valid (int_2_U |newVers#_165@0|)))
(< |oldVers#_164@0| (U_2_int (MapType2Select |unfoldingHeap#_155@0| this@@15 Node.valid)))
(= |unfoldingHeap#_155@1| |unfoldingHeap#_155@0|)) anon2_correct@@6)))))
(let ((anon0_correct@@7 (=> (! (and %lbl%+11476 true) :lblpos +11476) (=> (and
(< 0 |functionK#_179|)
(< (* 1000 |functionK#_179|) (Fractions 1))) (and
(! (or %lbl%@40090 (not (= this@@15 null))) :lblneg @40090)
(=> (not (= this@@15 null)) (=> (not (= this@@15 null)) (=> (and
(wf Heap@@7 ZeroMask ZeroMask)
(> (Fractions 100) 0)
(= Mask@0@@6 (MapType1Store ZeroMask this@@15 Node.valid (MapType0Store (MapType1Select ZeroMask this@@15 Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select ZeroMask this@@15 Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@0@@6)) (=> (and
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@15 Node.valid)))
(wf Heap@@7 Mask@0@@6 ZeroMask)
(wf Heap@@7 Mask@0@@6 ZeroMask)
(IsGoodMask Mask@0@@6)
(wf Heap@@7 Mask@0@@6 ZeroMask)
(= CurrentModule |module#default|)
(< 0 |unfoldingK#_160|)
(< (* 1000 |unfoldingK#_160|) (Fractions 1))) (and
(! (or %lbl%@40223 (=> true (not (= this@@15 null)))) :lblneg @40223)
(=> (=> true (not (= this@@15 null))) (=> (wf Heap@@7 Mask@0@@6 ZeroMask) (and
(! (or %lbl%@40247 (> (Fractions 100) 0)) :lblneg @40247)
(=> (> (Fractions 100) 0) (and
(! (or %lbl%@40255 (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@6 this@@15 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@6 this@@15 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@0@@6 this@@15 Node.valid) perm$N)))))) :lblneg @40255)
(=> (and
(<= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@6 this@@15 Node.valid) perm$R)))
(=> (= (Fractions 100) (U_2_int (MapType0Select (MapType1Select Mask@0@@6 this@@15 Node.valid) perm$R))) (<= 0 (U_2_int (MapType0Select (MapType1Select Mask@0@@6 this@@15 Node.valid) perm$N))))) (=> (= |unfoldingMask#_156@0| (MapType1Store Mask@0@@6 this@@15 Node.valid (MapType0Store (MapType1Select Mask@0@@6 this@@15 Node.valid) perm$R (int_2_U (- (U_2_int (MapType0Select (MapType1Select Mask@0@@6 this@@15 Node.valid) perm$R)) (Fractions 100)))))) (and
anon21_Then_correct@@0
anon21_Else_correct@@0))))))))))))))))))
(let ((PreconditionGeneratedEntry_correct@@7 (=> (! (and %lbl%+39942 true) :lblpos +39942) (=> (IsGoodMask Mask@@7) (=> (and
(IsGoodMask SecMask@@7)
(or
(= this@@15 null)
(= (dtype this@@15) |Node#t|))
(not (= this@@15 null))
(wf Heap@@7 Mask@@7 SecMask@@7)) anon0_correct@@7)))))
PreconditionGeneratedEntry_correct@@7))))))))))))))))))))
))
(check-sat)
(pop 1)
(declare-fun this@@16 () T@U)
(declare-fun Mask@1@@5 () T@U)
(declare-fun Mask@2@@3 () T@U)
(declare-fun Mask@3@@2 () T@U)
(declare-fun Mask@0@@7 () T@U)
(declare-fun %lbl%+12195 () Bool)
(declare-fun %lbl%+12193 () Bool)
(declare-fun %lbl%+12191 () Bool)
(declare-fun %lbl%@42250 () Bool)
(declare-fun %lbl%@42260 () Bool)
(declare-fun %lbl%@42272 () Bool)
(declare-fun %lbl%@42284 () Bool)
(declare-fun %lbl%@42294 () Bool)
(declare-fun %lbl%+12189 () Bool)
(declare-fun |predicateK#_180| () Int)
(declare-fun %lbl%@42202 () Bool)
(declare-fun %lbl%@42212 () Bool)
(declare-fun %lbl%+41898 () Bool)
(assert (and
(= (type this@@16) refType)
(= (type Mask@1@@5) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@2@@3) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@3@@2) (MapType1Type refType (MapType0Type PermissionComponentType intType)))
(= (type Mask@0@@7) (MapType1Type refType (MapType0Type PermissionComponentType intType)))))
(push 1)
(set-info :boogie-vc-id Node.valid$checkDefinedness)
(assert (not
(let ((anon2_correct@@7 (=> (! (and %lbl%+12195 true) :lblpos +12195) true)))
(let ((anon3_Else_correct@@0 (=> (! (and %lbl%+12193 true) :lblpos +12193) (=> (and
(= (MapType2Select Heap@@7 this@@16 Node.next) null)
(= Mask@3@@2 Mask@1@@5)) anon2_correct@@7))))
(let ((anon3_Then_correct@@0 (=> (! (and %lbl%+12191 true) :lblpos +12191) (=> (not (= (MapType2Select Heap@@7 this@@16 Node.next) null)) (and
(! (or %lbl%@42250 (=> true (not (= this@@16 null)))) :lblneg @42250)
(=> (=> true (not (= this@@16 null))) (and
(! (or %lbl%@42260 (=> true (CanRead Mask@1@@5 ZeroMask this@@16 Node.next))) :lblneg @42260)
(=> (=> true (CanRead Mask@1@@5 ZeroMask this@@16 Node.next)) (and
(! (or %lbl%@42272 (not (= (MapType2Select Heap@@7 this@@16 Node.next) null))) :lblneg @42272)
(=> (not (= (MapType2Select Heap@@7 this@@16 Node.next) null)) (and
(! (or %lbl%@42284 (=> true (not (= this@@16 null)))) :lblneg @42284)
(=> (=> true (not (= this@@16 null))) (and
(! (or %lbl%@42294 (=> true (CanRead Mask@1@@5 ZeroMask this@@16 Node.next))) :lblneg @42294)
(=> (=> true (CanRead Mask@1@@5 ZeroMask this@@16 Node.next)) (=> (not (= (MapType2Select Heap@@7 this@@16 Node.next) null)) (=> (and
(wf Heap@@7 Mask@1@@5 ZeroMask)
(> (Fractions 100) 0)
(= Mask@2@@3 (MapType1Store Mask@1@@5 (MapType2Select Heap@@7 this@@16 Node.next) Node.valid (MapType0Store (MapType1Select Mask@1@@5 (MapType2Select Heap@@7 this@@16 Node.next) Node.valid) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@1@@5 (MapType2Select Heap@@7 this@@16 Node.next) Node.valid) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@2@@3)
(IsGoodState (heapFragment (MapType2Select Heap@@7 (MapType2Select Heap@@7 this@@16 Node.next) Node.valid)))
(wf Heap@@7 Mask@2@@3 ZeroMask)
(wf Heap@@7 Mask@2@@3 ZeroMask)
(= Mask@3@@2 Mask@2@@3)) anon2_correct@@7))))))))))))))))
(let ((anon0_correct@@8 (=> (! (and %lbl%+12189 true) :lblpos +12189) (=> (and
(< 0 |predicateK#_180|)
(< (* 1000 |predicateK#_180|) (Fractions 1))
(not (= this@@16 null))) (=> (and
(wf Heap@@7 ZeroMask ZeroMask)
(or
(= (MapType2Select Heap@@7 this@@16 Node.next) null)
(= (dtype (MapType2Select Heap@@7 this@@16 Node.next)) |Node#t|))
(> (Fractions 100) 0)
(= Mask@0@@7 (MapType1Store ZeroMask this@@16 Node.next (MapType0Store (MapType1Select ZeroMask this@@16 Node.next) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select ZeroMask this@@16 Node.next) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@0@@7)
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@16 Node.next)))
(wf Heap@@7 Mask@0@@7 ZeroMask)
(wf Heap@@7 Mask@0@@7 ZeroMask)
(not (= this@@16 null))
(wf Heap@@7 Mask@0@@7 ZeroMask)
(> (Fractions 100) 0)
(= Mask@1@@5 (MapType1Store Mask@0@@7 this@@16 Node.value (MapType0Store (MapType1Select Mask@0@@7 this@@16 Node.value) perm$R (int_2_U (+ (U_2_int (MapType0Select (MapType1Select Mask@0@@7 this@@16 Node.value) perm$R)) (Fractions 100))))))
(IsGoodMask Mask@1@@5)
(IsGoodState (heapFragment (MapType2Select Heap@@7 this@@16 Node.value)))
(wf Heap@@7 Mask@1@@5 ZeroMask)
(wf Heap@@7 Mask@1@@5 ZeroMask)) (and
(! (or %lbl%@42202 (=> true (not (= this@@16 null)))) :lblneg @42202)
(=> (=> true (not (= this@@16 null))) (and
(! (or %lbl%@42212 (=> true (CanRead Mask@1@@5 ZeroMask this@@16 Node.next))) :lblneg @42212)
(=> (=> true (CanRead Mask@1@@5 ZeroMask this@@16 Node.next)) (and
anon3_Then_correct@@0
anon3_Else_correct@@0))))))))))
(let ((PreconditionGeneratedEntry_correct@@8 (=> (! (and %lbl%+41898 true) :lblpos +41898) (=> (IsGoodMask Mask@@7) (=> (and
(IsGoodMask SecMask@@7)
(or
(= this@@16 null)
(= (dtype this@@16) |Node#t|))
(not (= this@@16 null))
(wf Heap@@7 Mask@@7 SecMask@@7)) anon0_correct@@8)))))
PreconditionGeneratedEntry_correct@@8)))))
))
(check-sat)
(pop 1)
