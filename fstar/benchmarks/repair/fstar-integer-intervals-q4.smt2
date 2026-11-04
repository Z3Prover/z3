
(set-option :global-decls false)
(set-option :smt.mbqi false)
(set-option :auto_config false)
(set-option :produce-unsat-cores true)
(set-option :model true)
(set-option :smt.case_split 3)
(set-option :smt.relevancy 2)
(set-option :rewriter.enable_der false)
(set-option :rewriter.sort_disjunctions false)
(set-option :pi.decompose_patterns false)
(set-option :smt.arith.solver 6)


(declare-sort FString)
(declare-fun FString_constr_id (FString) Int)

(declare-sort Term)
(declare-sort Universe)
(declare-fun U_zero () Universe)
(declare-fun U_succ (Universe) Universe)
(declare-fun ulevel (Universe) Int)
(declare-fun Univ (Int) Universe)
(assert (= (ulevel U_zero) 0))
(assert (forall ((u Universe)) (! (= (ulevel (U_succ u)) (+ 1 (ulevel u))) :pattern ((ulevel (U_succ u))))))
(assert (forall ((u Universe)) (! (>= (ulevel u) 0) :pattern ((ulevel u)))))
(assert (forall ((u Universe)) (! (= (Univ (ulevel u)) u) :pattern ((ulevel u)))))
(assert (forall ((i Int)) (! (implies (>= i 0) (= (ulevel (Univ i)) i)) :pattern ((Univ i)))))
(declare-fun U_max (Universe Universe) Universe)
(assert (forall ((u1 Universe) (u2 Universe))
(! (= (U_max u1 u2)
(ite (<= (ulevel u1) (ulevel u2)) u2 u1))
:pattern ((U_max u1 u2)))))
(declare-fun U_unif (Int) Universe)
(declare-fun U_unknown () Universe)
(declare-fun Term_constr_id (Term) Int)
(declare-sort Dummy_sort)
(declare-fun Dummy_value () Dummy_sort)
(declare-datatypes () ((Fuel 
(ZFuel) 
(SFuel (prec Fuel)))))
(declare-fun MaxIFuel () Fuel)
(declare-fun MaxFuel () Fuel)
(declare-fun PreType (Term) Term)
(declare-fun Valid (Term) Bool)
(declare-fun HasTypeFuel (Fuel Term Term) Bool)
(define-fun HasTypeZ ((x Term) (t Term)) Bool
(HasTypeFuel ZFuel x t))
(define-fun HasType ((x Term) (t Term)) Bool
(HasTypeFuel MaxIFuel x t))
(declare-fun IsTotFun (Term) Bool)

(assert (forall ((f Fuel) (x Term) (t Term))
(! (= (HasTypeFuel (SFuel f) x t)
(HasTypeZ x t))
:pattern ((HasTypeFuel (SFuel f) x t)))))
(declare-fun NoHoist (Term Bool) Bool)
(assert (forall ((dummy Term) (b Bool))
(! (= (NoHoist dummy b) b)
:pattern ((NoHoist dummy b)))))
(define-fun  IsTyped ((x Term)) Bool
(exists ((t Term)) (HasTypeZ x t)))
(declare-fun ApplyTF (Term Fuel) Term)
(declare-fun ApplyTT (Term Term) Term)
(declare-fun Prec (Term Term) Bool)
(assert (forall ((x Term) (y Term) (z Term))
(! (implies (and (Prec x y) (Prec y z)) (Prec x z))
:pattern ((Prec x z) (Prec x y)))))
(assert (forall ((x Term) (y Term))
(implies (Prec x y)
(not (Prec y x)))))
(declare-fun Closure (Term) Term)
(declare-fun ConsTerm (Term Term) Term)
(declare-fun ConsFuel (Fuel Term) Term)
(declare-fun Tm_uvar (Int) Term)
(define-fun Reify ((x Term)) Term x)
(declare-fun Prims.precedes (Universe Universe Term Term Term Term) Term)
(declare-fun Range_const (Int) Term)
(declare-fun _mul (Int Int) Int)
(declare-fun _div (Int Int) Int)
(declare-fun _mod (Int Int) Int)
(declare-fun __uu__PartialApp () Term)
(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))
(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))
(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))
(declare-fun _rmul (Real Real) Real)
(declare-fun _rdiv (Real Real) Real)
(assert (forall ((x Real) (y Real)) (! (= (_rmul x y) (* x y)) :pattern ((_rmul x y)))))
(assert (forall ((x Real) (y Real)) (! (= (_rdiv x y) (/ x y)) :pattern ((_rdiv x y)))))
(define-fun Unreachable () Bool false); <start constructor FString_const>
(declare-fun FString_const (Int) FString)
(assert
 (! (forall ((@u0 Int))
   (! (= 0 (FString_constr_id (FString_const @u0)))
    :pattern ((FString_const @u0))
    :qid constructor_distinct_FString_const))
  :named constructor_distinct_FString_const))
(declare-fun FString_const_proj_0 (FString) Int)
(assert
 (! (forall ((@u0 Int))
   (! (= (FString_const_proj_0 (FString_const @u0)) @u0)
    :pattern ((FString_const @u0))
    :qid projection_inverse_FString_const_proj_0))
  :named projection_inverse_FString_const_proj_0))
(define-fun is-FString_const ((__@u0 FString)) Bool
 (and (= (FString_constr_id __@u0) 0) (= __@u0 (FString_const (FString_const_proj_0 __@u0)))))
(declare-fun Tm_type (Universe) Term)
(assert
 (! (forall ((@u0 Universe))
   (! (= 2 (Term_constr_id (Tm_type @u0)))
    :pattern ((Tm_type @u0))
    :qid constructor_distinct_Tm_type))
  :named constructor_distinct_Tm_type))
(declare-fun Tm_type_0 (Term) Universe)
(assert
 (! (forall ((@u0 Universe))
   (! (= (Tm_type_0 (Tm_type @u0)) @u0) :pattern ((Tm_type @u0)) :qid projection_inverse_Tm_type_0))
  :named projection_inverse_Tm_type_0))
(define-fun is-Tm_type ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 2) (= __@x0 (Tm_type (Tm_type_0 __@x0)))))
(declare-fun Tm_arrow (Int) Term)
(assert
 (! (forall ((@u0 Int))
   (! (= 3 (Term_constr_id (Tm_arrow @u0)))
    :pattern ((Tm_arrow @u0))
    :qid constructor_distinct_Tm_arrow))
  :named constructor_distinct_Tm_arrow))
(declare-fun Tm_arrow_id (Term) Int)
(assert
 (! (forall ((@u0 Int))
   (! (= (Tm_arrow_id (Tm_arrow @u0)) @u0)
    :pattern ((Tm_arrow @u0))
    :qid projection_inverse_Tm_arrow_id))
  :named projection_inverse_Tm_arrow_id))
(define-fun is-Tm_arrow ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 3) (= __@x0 (Tm_arrow (Tm_arrow_id __@x0)))))
(declare-fun Tm_unit () Term)
(assert (! (= 6 (Term_constr_id Tm_unit)) :named constructor_distinct_Tm_unit))
(define-fun is-Tm_unit ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 6) (= __@x0 Tm_unit)))
(declare-fun BoxInt (Int) Term)
(assert
 (! (forall ((@u0 Int))
   (! (= 7 (Term_constr_id (BoxInt @u0))) :pattern ((BoxInt @u0)) :qid constructor_distinct_BoxInt))
  :named constructor_distinct_BoxInt))
(declare-fun BoxInt_proj_0 (Term) Int)
(assert
 (! (forall ((@u0 Int))
   (! (= (BoxInt_proj_0 (BoxInt @u0)) @u0)
    :pattern ((BoxInt @u0))
    :qid projection_inverse_BoxInt_proj_0))
  :named projection_inverse_BoxInt_proj_0))
(define-fun is-BoxInt ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 7) (= __@x0 (BoxInt (BoxInt_proj_0 __@x0)))))
(declare-fun BoxBool (Bool) Term)
(assert
 (! (forall ((@u0 Bool))
   (! (= 8 (Term_constr_id (BoxBool @u0)))
    :pattern ((BoxBool @u0))
    :qid constructor_distinct_BoxBool))
  :named constructor_distinct_BoxBool))
(declare-fun BoxBool_proj_0 (Term) Bool)
(assert
 (! (forall ((@u0 Bool))
   (! (= (BoxBool_proj_0 (BoxBool @u0)) @u0)
    :pattern ((BoxBool @u0))
    :qid projection_inverse_BoxBool_proj_0))
  :named projection_inverse_BoxBool_proj_0))
(define-fun is-BoxBool ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 8) (= __@x0 (BoxBool (BoxBool_proj_0 __@x0)))))
(declare-fun BoxString (FString) Term)
(assert
 (! (forall ((@u0 FString))
   (! (= 9 (Term_constr_id (BoxString @u0)))
    :pattern ((BoxString @u0))
    :qid constructor_distinct_BoxString))
  :named constructor_distinct_BoxString))
(declare-fun BoxString_proj_0 (Term) FString)
(assert
 (! (forall ((@u0 FString))
   (! (= (BoxString_proj_0 (BoxString @u0)) @u0)
    :pattern ((BoxString @u0))
    :qid projection_inverse_BoxString_proj_0))
  :named projection_inverse_BoxString_proj_0))
(define-fun is-BoxString ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 9) (= __@x0 (BoxString (BoxString_proj_0 __@x0)))))
(declare-fun BoxReal (Real) Term)
(assert
 (! (forall ((@u0 Real))
   (! (= 10 (Term_constr_id (BoxReal @u0)))
    :pattern ((BoxReal @u0))
    :qid constructor_distinct_BoxReal))
  :named constructor_distinct_BoxReal))
(declare-fun BoxReal_proj_0 (Term) Real)
(assert
 (! (forall ((@u0 Real))
   (! (= (BoxReal_proj_0 (BoxReal @u0)) @u0)
    :pattern ((BoxReal @u0))
    :qid projection_inverse_BoxReal_proj_0))
  :named projection_inverse_BoxReal_proj_0))
(define-fun is-BoxReal ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 10) (= __@x0 (BoxReal (BoxReal_proj_0 __@x0)))))
(declare-fun LexCons (Term Term Term) Term)
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= 11 (Term_constr_id (LexCons @x0 @x1 @x2)))
    :pattern ((LexCons @x0 @x1 @x2))
    :qid constructor_distinct_LexCons))
  :named constructor_distinct_LexCons))
(declare-fun LexCons_0 (Term) Term)
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (LexCons_0 (LexCons @x0 @x1 @x2)) @x0)
    :pattern ((LexCons @x0 @x1 @x2))
    :qid projection_inverse_LexCons_0))
  :named projection_inverse_LexCons_0))
(declare-fun LexCons_1 (Term) Term)
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (LexCons_1 (LexCons @x0 @x1 @x2)) @x1)
    :pattern ((LexCons @x0 @x1 @x2))
    :qid projection_inverse_LexCons_1))
  :named projection_inverse_LexCons_1))
(declare-fun LexCons_2 (Term) Term)
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (LexCons_2 (LexCons @x0 @x1 @x2)) @x2)
    :pattern ((LexCons @x0 @x1 @x2))
    :qid projection_inverse_LexCons_2))
  :named projection_inverse_LexCons_2))
(define-fun is-LexCons ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 11)
  (= __@x0 (LexCons (LexCons_0 __@x0) (LexCons_1 __@x0) (LexCons_2 __@x0)))))
(declare-fun Prims.precedes@tok (Universe Universe) Term)
(assert
(forall ((u0 Universe) (u1 Universe) (@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
(! (= (ApplyTT (ApplyTT (ApplyTT (ApplyTT (Prims.precedes@tok u0 u1) @x0) @x1) @x2) @x3)
(Prims.precedes u0 u1 @x0 @x1 @x2 @x3))
:pattern ((ApplyTT (ApplyTT (ApplyTT (ApplyTT (Prims.precedes@tok u0 u1) @x0) @x1) @x2) @x3)))))

(define-fun is-Prims.LexCons ((t Term)) Bool 
(is-LexCons t))
(declare-fun Prims.lex_t () Term)
(declare-fun LexTop () Term)
(assert (forall ((u0 Universe) (u1 Universe) (t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))
(iff (Valid (Prims.precedes u0 u1 Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))
(or (Valid (Prims.precedes u0 u1 t1 t2 x1 y1))
(and (= x1 y1)
(Valid (Prims.precedes u0 u1 Prims.lex_t Prims.lex_t x2 y2)))))))
(assert (forall ((u0 Universe) (u1 Universe) (t1 Term) (t2 Term) (e1 Term) (e2 Term))
(! (iff (Valid (Prims.precedes u0 u1 t1 t2 e1 e2))
(Valid (Prims.precedes U_zero U_zero Prims.lex_t Prims.lex_t e1 e2)))
:pattern (Prims.precedes u0 u1 t1 t2 e1 e2))))
(assert (forall ((u0 Universe) (u1 Universe) (t1 Term) (t2 Term))
(! (iff (Valid (Prims.precedes u0 u1 Prims.lex_t Prims.lex_t t1 t2)) 
(Prec t1 t2))
:pattern ((Prims.precedes u0 u1 Prims.lex_t Prims.lex_t t1 t2)))))
(assert (forall ((u Universe) (t Term))
(! (iff (HasType (Tm_type u) t)
(= t (Tm_type (U_succ u))))
:pattern ((HasType (Tm_type u) t)))))

(declare-fun FStar.IntegerIntervals.greater_than (Term) Term)
(declare-fun Prims.eqtype () Term)
(declare-fun Prims.hasEq (Universe Term) Term)
(declare-fun Prims.int () Term)
(declare-fun Prims.op_Addition (Term Term) Term)
(declare-fun Prims.op_Subtraction (Term Term) Term)
(declare-fun Prims.prop () Term)
(declare-fun Tm_refine_25948cf2cb84e8edfffe30eaf3d63408 (Term) Term)
(declare-fun Tm_refine_9d6af3f3535473623f7aec2f0501897f () Term)
(assert
 (! (= 298 (Term_constr_id Prims.int)) :named constructor_distinct_Prims.int))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(24,5-24,17); use=FStar.IntegerIntervals.fst(24,5-24,17)
  (forall ((@x0 Term))
   (! (= (FStar.IntegerIntervals.greater_than @x0) (Tm_refine_25948cf2cb84e8edfffe30eaf3d63408 @x0))
    :pattern ((FStar.IntegerIntervals.greater_than @x0))
    :qid equation_FStar.IntegerIntervals.greater_than))
  :named equation_FStar.IntegerIntervals.greater_than))
(assert
 (! (= Prims.eqtype Tm_refine_9d6af3f3535473623f7aec2f0501897f) :named equation_Prims.eqtype))
(assert
 (! (HasType Prims.eqtype (Tm_type (U_succ U_zero))) :named function_token_typing_Prims.eqtype))
(assert
 (! (HasType Prims.int Prims.eqtype) :named function_token_typing_Prims.int))
(assert
 (! (HasType Prims.prop (Tm_type U_zero)) :named function_token_typing_Prims.prop))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(24,29-24,39); use=FStar.IntegerIntervals.fst(24,29-24,39)
  (forall ((@x0 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_25948cf2cb84e8edfffe30eaf3d63408 @x0)))
     (Valid (Prims.hasEq U_zero Prims.int)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_25948cf2cb84e8edfffe30eaf3d63408 @x0))))
    :qid haseqTm_refine_25948cf2cb84e8edfffe30eaf3d63408))
  :named haseqTm_refine_25948cf2cb84e8edfffe30eaf3d63408))
(assert
 (! (iff
   (Valid (Prims.hasEq (U_succ U_zero) Tm_refine_9d6af3f3535473623f7aec2f0501897f))
   (Valid (Prims.hasEq (U_succ U_zero) (Tm_type U_zero))))
  :named haseqTm_refine_9d6af3f3535473623f7aec2f0501897f))
(assert
 (! (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.int) (is-BoxInt @x1))
    :pattern ((HasTypeFuel @u0 @x1 Prims.int))
    :qid int_inversion))
  :named int_inversion))
(assert
 (! (forall ((@u0 Int)) (! (HasType (BoxInt @u0) Prims.int) :pattern ((BoxInt @u0)) :qid int_typing))
  :named int_typing))
(assert
 (! ;; def=Prims.fst(520,4-520,15); use=Prims.fst(520,4-520,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_Addition @x0 @x1) (BoxInt (+ (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_Addition @x0 @x1))
    :qid primitive_Prims.op_Addition))
  :named primitive_Prims.op_Addition))
(assert
 (! ;; def=Prims.fst(514,4-514,18); use=Prims.fst(514,4-514,18)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_Subtraction @x0 @x1) (BoxInt (- (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_Subtraction @x0 @x1))
    :qid primitive_Prims.op_Subtraction))
  :named primitive_Prims.op_Subtraction))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(24,29-24,39); use=FStar.IntegerIntervals.fst(24,29-24,39)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_25948cf2cb84e8edfffe30eaf3d63408 @x2))
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      (> (BoxInt_proj_0 @x1) (BoxInt_proj_0 @x2))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_25948cf2cb84e8edfffe30eaf3d63408 @x2)))
    :qid refinement_interpretation_Tm_refine_25948cf2cb84e8edfffe30eaf3d63408))
  :named refinement_interpretation_Tm_refine_25948cf2cb84e8edfffe30eaf3d63408))
(assert
 (! ;; def=Prims.fst(90,14-90,31); use=Prims.fst(90,14-90,31)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_9d6af3f3535473623f7aec2f0501897f)
     (and
      (HasTypeFuel @u0 @x1 (Tm_type U_zero))
      (Valid
       (Prims.hasEq U_zero @x1))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_9d6af3f3535473623f7aec2f0501897f))
    :qid refinement_interpretation_Tm_refine_9d6af3f3535473623f7aec2f0501897f))
  :named refinement_interpretation_Tm_refine_9d6af3f3535473623f7aec2f0501897f))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(24,29-24,39); use=FStar.IntegerIntervals.fst(24,29-24,39)
  (forall ((@x0 Term))
   (! (HasType (Tm_refine_25948cf2cb84e8edfffe30eaf3d63408 @x0) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_25948cf2cb84e8edfffe30eaf3d63408 @x0) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_25948cf2cb84e8edfffe30eaf3d63408))
  :named refinement_kinding_Tm_refine_25948cf2cb84e8edfffe30eaf3d63408))
(assert
 (! (HasType Tm_refine_9d6af3f3535473623f7aec2f0501897f (Tm_type (U_succ U_zero)))
  :named refinement_kinding_Tm_refine_9d6af3f3535473623f7aec2f0501897f))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(24,5-24,17); use=FStar.IntegerIntervals.fst(24,5-24,17)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 Prims.int)
     (HasType (FStar.IntegerIntervals.greater_than @x0) (Tm_type U_zero)))
    :pattern ((FStar.IntegerIntervals.greater_than @x0))
    :qid typing_FStar.IntegerIntervals.greater_than))
  :named typing_FStar.IntegerIntervals.greater_than))
(assert
 (! (HasType Prims.eqtype (Tm_type (U_succ U_zero))) :named typing_Prims.eqtype))
(assert
 (! ;; def=Prims.fst(86,5-86,10); use=Prims.fst(86,5-86,10)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies (HasType @x1 (Tm_type @u0)) (HasType (Prims.hasEq @u0 @x1) Prims.prop))
    :pattern ((Prims.hasEq @u0 @x1))
    :qid typing_Prims.hasEq))
  :named typing_Prims.hasEq))
(assert
 (! (HasType Prims.int Prims.eqtype) :named typing_Prims.int))
(assert
 (! ;; def=Prims.fst(520,4-520,15); use=Prims.fst(520,4-520,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Prims.int) (HasType @x1 Prims.int))
     (HasType (Prims.op_Addition @x0 @x1) Prims.int))
    :pattern ((Prims.op_Addition @x0 @x1))
    :qid typing_Prims.op_Addition))
  :named typing_Prims.op_Addition))
(assert
 (! ;; def=Prims.fst(514,4-514,18); use=Prims.fst(514,4-514,18)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Prims.int) (HasType @x1 Prims.int))
     (HasType (Prims.op_Subtraction @x0 @x1) Prims.int))
    :pattern ((Prims.op_Subtraction @x0 @x1))
    :qid typing_Prims.op_Subtraction))
  :named typing_Prims.op_Subtraction))
(assert
 (! (HasType Prims.prop (Tm_type U_zero)) :named typing_Prims.prop))
(declare-fun FStar.IntegerIntervals.ifrom_ito (Term Term) Term)
(declare-fun FStar.IntegerIntervals.interval (Term Term) Term)
(declare-fun FStar.IntegerIntervals.interval_condition (Term Term Term) Term)
(declare-fun FStar.IntegerIntervals.interval_type (Term Term) Term)
(declare-fun Prims.bool () Term)
(declare-fun Prims.l_True () Term)
(declare-fun Prims.op_AmpAmp (Term Term) Term)
(declare-fun Prims.op_LessThan (Term Term) Term)
(declare-fun Prims.op_LessThanOrEqual (Term Term) Term)
(declare-fun Prims.pure_post (Universe Term) Term)
(declare-fun Prims.pure_post_ (Universe Term Term) Term)
(declare-fun Prims.unit () Term)
(declare-fun Tm_arrow_eed220cc6714c2e2d27bc073c82dad19 (Universe Term Term) Term)
(declare-fun Tm_refine_97ae7a69cd5f02d44d6644f169486ebb (Term Term) Term)
(declare-fun Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 (Universe Term Term) Term)
(declare-fun Tm_refine_fcf1a3596fffd49dd2e91f2678358f19 (Term Term) Term)
(assert
 (! ;; def=Prims.fst(281,39-281,56); use=Prims.fst(281,39-281,56)
  (forall ((@x0 Term) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_eed220cc6714c2e2d27bc073c82dad19 @u1 @x2 @x3))
     (and
      (forall ((@x4 Term))
       (! (implies
         (HasType @x4 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u1 @x2 @x3))
         (HasType (ApplyTT @x0 @x4) Prims.prop))
        :pattern ((ApplyTT @x0 @x4))
        :qid Prims_interpretation_Tm_arrow_eed220cc6714c2e2d27bc073c82dad19.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 (Tm_arrow_eed220cc6714c2e2d27bc073c82dad19 @u1 @x2 @x3)))
    :qid Prims_interpretation_Tm_arrow_eed220cc6714c2e2d27bc073c82dad19))
  :named Prims_interpretation_Tm_arrow_eed220cc6714c2e2d27bc073c82dad19))
(assert
 (! (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.bool) (is-BoxBool @x1))
    :pattern ((HasTypeFuel @u0 @x1 Prims.bool))
    :qid bool_inversion))
  :named bool_inversion))
(assert
 (! (forall ((@u0 Bool))
   (! (HasType (BoxBool @u0) Prims.bool) :pattern ((BoxBool @u0)) :qid bool_typing))
  :named bool_typing))
(assert
 (! (= 107 (Term_constr_id Prims.bool)) :named constructor_distinct_Prims.bool))
(assert
 (! (= 125 (Term_constr_id Prims.unit)) :named constructor_distinct_Prims.unit))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(44,5-44,14); use=FStar.IntegerIntervals.fst(44,5-44,14)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (FStar.IntegerIntervals.ifrom_ito @x0 @x1)
     (FStar.IntegerIntervals.interval @x0 (Prims.op_Addition @x1 (BoxInt 1))))
    :pattern ((FStar.IntegerIntervals.ifrom_ito @x0 @x1))
    :qid equation_FStar.IntegerIntervals.ifrom_ito))
  :named equation_FStar.IntegerIntervals.ifrom_ito))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(38,5-38,13); use=FStar.IntegerIntervals.fst(38,5-38,13)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (FStar.IntegerIntervals.interval @x0 @x1)
     (Tm_refine_fcf1a3596fffd49dd2e91f2678358f19 @x0 @x1))
    :pattern ((FStar.IntegerIntervals.interval @x0 @x1))
    :qid equation_FStar.IntegerIntervals.interval))
  :named equation_FStar.IntegerIntervals.interval))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(33,4-33,22); use=FStar.IntegerIntervals.fst(33,4-33,22)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (=
     (FStar.IntegerIntervals.interval_condition @x0 @x1 @x2)
     (Prims.op_AmpAmp (Prims.op_LessThanOrEqual @x0 @x2) (Prims.op_LessThan @x2 @x1)))
    :pattern ((FStar.IntegerIntervals.interval_condition @x0 @x1 @x2))
    :qid equation_FStar.IntegerIntervals.interval_condition))
  :named equation_FStar.IntegerIntervals.interval_condition))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(35,5-35,18); use=FStar.IntegerIntervals.fst(35,5-35,18)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (FStar.IntegerIntervals.interval_type @x0 @x1)
     (Tm_refine_97ae7a69cd5f02d44d6644f169486ebb @x0 @x1))
    :pattern ((FStar.IntegerIntervals.interval_type @x0 @x1))
    :qid equation_FStar.IntegerIntervals.interval_type))
  :named equation_FStar.IntegerIntervals.interval_type))
(assert
 (! ;; def=Prims.fst(282,4-282,13); use=Prims.fst(282,4-282,13)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= (Prims.pure_post @u0 @x1) (Prims.pure_post_ @u0 @x1 Prims.l_True))
    :pattern ((Prims.pure_post @u0 @x1))
    :qid equation_Prims.pure_post))
  :named equation_Prims.pure_post))
(assert
 (! ;; def=Prims.fst(281,4-281,14); use=Prims.fst(281,4-281,14)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (= (Prims.pure_post_ @u0 @x1 @x2) (Tm_arrow_eed220cc6714c2e2d27bc073c82dad19 @u0 @x2 @x1))
    :pattern ((Prims.pure_post_ @u0 @x1 @x2))
    :qid equation_Prims.pure_post_))
  :named equation_Prims.pure_post_))
(assert
 (! (HasType Prims.bool Prims.eqtype) :named function_token_typing_Prims.bool))
(assert
 (! (HasType Prims.l_True Prims.prop) :named function_token_typing_Prims.l_True))
(assert
 (! (HasType Prims.unit Prims.eqtype) :named function_token_typing_Prims.unit))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(35,31-35,80); use=FStar.IntegerIntervals.fst(35,31-35,80)
  (forall ((@x0 Term) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq (U_succ U_zero) (Tm_refine_97ae7a69cd5f02d44d6644f169486ebb @x0 @x1)))
     (Valid (Prims.hasEq (U_succ U_zero) (Tm_type U_zero))))
    :pattern
     ((Valid (Prims.hasEq (U_succ U_zero) (Tm_refine_97ae7a69cd5f02d44d6644f169486ebb @x0 @x1))))
    :qid haseqTm_refine_97ae7a69cd5f02d44d6644f169486ebb))
  :named haseqTm_refine_97ae7a69cd5f02d44d6644f169486ebb))
(assert
 (! ;; def=Prims.fst(281,39-281,48); use=Prims.fst(281,39-281,48)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (iff
     (Valid (Prims.hasEq @u0 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2)))
     (Valid (Prims.hasEq @u0 @x2)))
    :pattern ((Valid (Prims.hasEq @u0 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2))))
    :qid haseqTm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
  :named haseqTm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(35,47-35,78); use=FStar.IntegerIntervals.fst(35,47-35,78)
  (forall ((@x0 Term) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_fcf1a3596fffd49dd2e91f2678358f19 @x0 @x1)))
     (Valid (Prims.hasEq U_zero Prims.int)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_fcf1a3596fffd49dd2e91f2678358f19 @x0 @x1))))
    :qid haseqTm_refine_fcf1a3596fffd49dd2e91f2678358f19))
  :named haseqTm_refine_fcf1a3596fffd49dd2e91f2678358f19))
(assert
 (! ;; def=Prims.fst(281,39-281,56); use=Prims.fst(281,39-281,56)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (HasType (Tm_arrow_eed220cc6714c2e2d27bc073c82dad19 @u0 @x1 @x2) (Tm_type @u0))
    :pattern ((HasType (Tm_arrow_eed220cc6714c2e2d27bc073c82dad19 @u0 @x1 @x2) (Tm_type @u0)))
    :qid kinding_Tm_arrow_eed220cc6714c2e2d27bc073c82dad19))
  :named kinding_Tm_arrow_eed220cc6714c2e2d27bc073c82dad19))
(assert
 (! ;; def=Prims.fst(490,4-490,13); use=Prims.fst(490,4-490,13)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_AmpAmp @x0 @x1) (BoxBool (and (BoxBool_proj_0 @x0) (BoxBool_proj_0 @x1))))
    :pattern ((Prims.op_AmpAmp @x0 @x1))
    :qid primitive_Prims.op_AmpAmp))
  :named primitive_Prims.op_AmpAmp))
(assert
 (! ;; def=Prims.fst(550,4-550,15); use=Prims.fst(550,4-550,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_LessThan @x0 @x1) (BoxBool (< (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_LessThan @x0 @x1))
    :qid primitive_Prims.op_LessThan))
  :named primitive_Prims.op_LessThan))
(assert
 (! ;; def=Prims.fst(532,4-532,22); use=Prims.fst(532,4-532,22)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_LessThanOrEqual @x0 @x1) (BoxBool (<= (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_LessThanOrEqual @x0 @x1))
    :qid primitive_Prims.op_LessThanOrEqual))
  :named primitive_Prims.op_LessThanOrEqual))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(35,31-35,80); use=FStar.IntegerIntervals.fst(35,31-35,80)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_97ae7a69cd5f02d44d6644f169486ebb @x2 @x3))
     (and
      (HasTypeFuel @u0 @x1 (Tm_type U_zero))
      (= @x1 (Tm_refine_fcf1a3596fffd49dd2e91f2678358f19 @x2 @x3))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_97ae7a69cd5f02d44d6644f169486ebb @x2 @x3)))
    :qid refinement_interpretation_Tm_refine_97ae7a69cd5f02d44d6644f169486ebb))
  :named refinement_interpretation_Tm_refine_97ae7a69cd5f02d44d6644f169486ebb))
(assert
 (! ;; def=Prims.fst(281,39-281,48); use=Prims.fst(281,39-281,48)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u2 @x3 @x4))
     (and
      (HasTypeFuel @u0 @x1 @x4)
      (Valid
       @x3)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u2 @x3 @x4)))
    :qid refinement_interpretation_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
  :named refinement_interpretation_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(35,47-35,78); use=FStar.IntegerIntervals.fst(35,47-35,78)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_fcf1a3596fffd49dd2e91f2678358f19 @x2 @x3))
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      (BoxBool_proj_0 (FStar.IntegerIntervals.interval_condition @x2 @x3 @x1))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_fcf1a3596fffd49dd2e91f2678358f19 @x2 @x3)))
    :qid refinement_interpretation_Tm_refine_fcf1a3596fffd49dd2e91f2678358f19))
  :named refinement_interpretation_Tm_refine_fcf1a3596fffd49dd2e91f2678358f19))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(35,31-35,80); use=FStar.IntegerIntervals.fst(35,31-35,80)
  (forall ((@x0 Term) (@x1 Term))
   (! (HasType (Tm_refine_97ae7a69cd5f02d44d6644f169486ebb @x0 @x1) (Tm_type (U_succ U_zero)))
    :pattern
     ((HasType (Tm_refine_97ae7a69cd5f02d44d6644f169486ebb @x0 @x1) (Tm_type (U_succ U_zero))))
    :qid refinement_kinding_Tm_refine_97ae7a69cd5f02d44d6644f169486ebb))
  :named refinement_kinding_Tm_refine_97ae7a69cd5f02d44d6644f169486ebb))
(assert
 (! ;; def=Prims.fst(281,39-281,48); use=Prims.fst(281,39-281,48)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (HasType (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2) (Tm_type @u0))
    :pattern ((HasType (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2) (Tm_type @u0)))
    :qid refinement_kinding_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
  :named refinement_kinding_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(35,47-35,78); use=FStar.IntegerIntervals.fst(35,47-35,78)
  (forall ((@x0 Term) (@x1 Term))
   (! (HasType (Tm_refine_fcf1a3596fffd49dd2e91f2678358f19 @x0 @x1) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_fcf1a3596fffd49dd2e91f2678358f19 @x0 @x1) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_fcf1a3596fffd49dd2e91f2678358f19))
  :named refinement_kinding_Tm_refine_fcf1a3596fffd49dd2e91f2678358f19))
(assert (! (Valid Prims.l_True) :named true_interp))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(44,5-44,14); use=FStar.IntegerIntervals.fst(44,5-44,14)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Prims.int) (HasType @x1 Prims.int))
     (HasType
      (FStar.IntegerIntervals.ifrom_ito @x0 @x1)
      (FStar.IntegerIntervals.interval_type @x0 (Prims.op_Addition @x1 (BoxInt 1)))))
    :pattern ((FStar.IntegerIntervals.ifrom_ito @x0 @x1))
    :qid typing_FStar.IntegerIntervals.ifrom_ito))
  :named typing_FStar.IntegerIntervals.ifrom_ito))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(38,5-38,13); use=FStar.IntegerIntervals.fst(38,5-38,13)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Prims.int) (HasType @x1 Prims.int))
     (HasType
      (FStar.IntegerIntervals.interval @x0 @x1)
      (FStar.IntegerIntervals.interval_type @x0 @x1)))
    :pattern ((FStar.IntegerIntervals.interval @x0 @x1))
    :qid typing_FStar.IntegerIntervals.interval))
  :named typing_FStar.IntegerIntervals.interval))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(33,4-33,22); use=FStar.IntegerIntervals.fst(33,4-33,22)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x0 Prims.int) (HasType @x1 Prims.int) (HasType @x2 Prims.int))
     (HasType (FStar.IntegerIntervals.interval_condition @x0 @x1 @x2) Prims.bool))
    :pattern ((FStar.IntegerIntervals.interval_condition @x0 @x1 @x2))
    :qid typing_FStar.IntegerIntervals.interval_condition))
  :named typing_FStar.IntegerIntervals.interval_condition))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(35,5-35,18); use=FStar.IntegerIntervals.fst(35,5-35,18)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Prims.int) (HasType @x1 Prims.int))
     (HasType (FStar.IntegerIntervals.interval_type @x0 @x1) (Tm_type (U_succ U_zero))))
    :pattern ((FStar.IntegerIntervals.interval_type @x0 @x1))
    :qid typing_FStar.IntegerIntervals.interval_type))
  :named typing_FStar.IntegerIntervals.interval_type))
(assert
 (! (HasType Prims.bool Prims.eqtype) :named typing_Prims.bool))
(assert
 (! (HasType Prims.l_True Prims.prop) :named typing_Prims.l_True))
(assert
 (! ;; def=Prims.fst(490,4-490,13); use=Prims.fst(490,4-490,13)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Prims.bool) (HasType @x1 Prims.bool))
     (HasType (Prims.op_AmpAmp @x0 @x1) Prims.bool))
    :pattern ((Prims.op_AmpAmp @x0 @x1))
    :qid typing_Prims.op_AmpAmp))
  :named typing_Prims.op_AmpAmp))
(assert
 (! ;; def=Prims.fst(550,4-550,15); use=Prims.fst(550,4-550,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Prims.int) (HasType @x1 Prims.int))
     (HasType (Prims.op_LessThan @x0 @x1) Prims.bool))
    :pattern ((Prims.op_LessThan @x0 @x1))
    :qid typing_Prims.op_LessThan))
  :named typing_Prims.op_LessThan))
(assert
 (! ;; def=Prims.fst(532,4-532,22); use=Prims.fst(532,4-532,22)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Prims.int) (HasType @x1 Prims.int))
     (HasType (Prims.op_LessThanOrEqual @x0 @x1) Prims.bool))
    :pattern ((Prims.op_LessThanOrEqual @x0 @x1))
    :qid typing_Prims.op_LessThanOrEqual))
  :named typing_Prims.op_LessThanOrEqual))
(assert
 (! ;; def=Prims.fst(282,4-282,13); use=Prims.fst(282,4-282,13)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies (HasType @x1 (Tm_type @u0)) (HasType (Prims.pure_post @u0 @x1) (Tm_type @u0)))
    :pattern ((Prims.pure_post @u0 @x1))
    :qid typing_Prims.pure_post))
  :named typing_Prims.pure_post))
(assert
 (! ;; def=Prims.fst(281,4-281,14); use=Prims.fst(281,4-281,14)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 Prims.prop))
     (HasType (Prims.pure_post_ @u0 @x1 @x2) (Tm_type @u0)))
    :pattern ((Prims.pure_post_ @u0 @x1 @x2))
    :qid typing_Prims.pure_post_))
  :named typing_Prims.pure_post_))
(assert
 (! (HasType Prims.unit Prims.eqtype) :named typing_Prims.unit))
(assert
 (! (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.unit) (= @x1 Tm_unit))
    :pattern ((HasTypeFuel @u0 @x1 Prims.unit))
    :qid unit_inversion))
  :named unit_inversion))
(assert
 (! (HasType Tm_unit Prims.unit) :named unit_typing))
(declare-fun Prims.guard_free (Term) Term)
(declare-fun Prims.nat () Term)
(declare-fun Prims.op_GreaterThanOrEqual (Term Term) Term)
(declare-fun Tm_refine_542f9d4f129664613f2483a6c88bc7c2 () Term)
(assert
 (! (= Prims.nat Tm_refine_542f9d4f129664613f2483a6c88bc7c2) :named equation_Prims.nat))
(assert
 (! (HasType Prims.nat (Tm_type U_zero)) :named function_token_typing_Prims.nat))
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
   (Valid (Prims.hasEq U_zero Prims.int)))
  :named haseqTm_refine_542f9d4f129664613f2483a6c88bc7c2))
(assert
 (! ;; def=Prims.fst(544,4-544,25); use=Prims.fst(544,4-544,25)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (Prims.op_GreaterThanOrEqual @x0 @x1)
     (BoxBool (>= (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_GreaterThanOrEqual @x0 @x1))
    :qid primitive_Prims.op_GreaterThanOrEqual))
  :named primitive_Prims.op_GreaterThanOrEqual))
(assert
 (! ;; def=Prims.fst(642,11-642,25); use=Prims.fst(642,11-642,25)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_542f9d4f129664613f2483a6c88bc7c2)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      (>= (BoxInt_proj_0 @x1) (BoxInt_proj_0 (BoxInt 0)))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
    :qid refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
  :named refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
(assert
 (! (HasType Tm_refine_542f9d4f129664613f2483a6c88bc7c2 (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
(assert
 (! ;; def=Prims.fst(312,5-312,15); use=Prims.fst(312,5-312,15)
  (forall ((@x0 Term))
   (! (implies (HasType @x0 Prims.prop) (HasType (Prims.guard_free @x0) Prims.prop))
    :pattern ((Prims.guard_free @x0))
    :qid typing_Prims.guard_free))
  :named typing_Prims.guard_free))
(assert
 (! (HasType Prims.nat (Tm_type U_zero)) :named typing_Prims.nat))
(assert
 (! ;; def=Prims.fst(544,4-544,25); use=Prims.fst(544,4-544,25)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Prims.int) (HasType @x1 Prims.int))
     (HasType (Prims.op_GreaterThanOrEqual @x0 @x1) Prims.bool))
    :pattern ((Prims.op_GreaterThanOrEqual @x0 @x1))
    :qid typing_Prims.op_GreaterThanOrEqual))
  :named typing_Prims.op_GreaterThanOrEqual))
(declare-fun FStar.IntegerIntervals.interval_size (Term Term Term) Term)
(assert
 (! ;; def=FStar.IntegerIntervals.fst(54,4-54,17); use=FStar.IntegerIntervals.fst(54,4-54,17)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (=
     (FStar.IntegerIntervals.interval_size @x0 @x1 @x2)
     (let ((@lb3 (Prims.op_GreaterThanOrEqual @x1 @x0)))
      (ite (= @lb3 (BoxBool true)) (Prims.op_Subtraction @x1 @x0) (BoxInt 0))))
    :pattern ((FStar.IntegerIntervals.interval_size @x0 @x1 @x2))
    :qid equation_FStar.IntegerIntervals.interval_size))
  :named equation_FStar.IntegerIntervals.interval_size))
(assert
 (! ;; def=FStar.IntegerIntervals.fst(54,4-54,17); use=FStar.IntegerIntervals.fst(54,4-54,17)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (implies
     (and
      (HasType @x0 Prims.int)
      (HasType @x1 Prims.int)
      (HasType @x2 (FStar.IntegerIntervals.interval_type @x0 @x1)))
     (HasType (FStar.IntegerIntervals.interval_size @x0 @x1 @x2) Prims.nat))
    :pattern ((FStar.IntegerIntervals.interval_size @x0 @x1 @x2))
    :qid typing_FStar.IntegerIntervals.interval_size))
  :named typing_FStar.IntegerIntervals.interval_size))
(push) ;; push{1
(declare-fun label_1 () Bool)
(push) ;; push{0
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
(assert
 (! (not
   (or
    label_1
    (=
     (FStar.IntegerIntervals.interval_size
      (BoxInt 5)
      (BoxInt 10)
      (FStar.IntegerIntervals.interval (BoxInt 5) (BoxInt 10)))
     (BoxInt 5))))
  :named @query))
(set-option :rlimit 2500000)
(check-sat)