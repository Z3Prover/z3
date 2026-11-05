module Z3ArrayEqualityTests

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module A = Z3ArrayEquality
module B = Z3BooleanRewrite
module N = Z3TheoryNormalize
module T = Z3ArrayTheory

let int_s = BaseSort "Int"
let zero = A.integer 0
let one = A.integer 1
let two = A.integer 2
let three = A.integer 3
let constant (s:sort) (v:expr) : expr =
  App { decl_name = "const"; domain = [get_sort v]; range = s;
        interp = Some op_const_array; int_params = [] } [v]
let store (a k v:expr) : expr =
  App { decl_name = "store"; domain = [get_sort a; get_sort k; get_sort v];
        range = get_sort a; interp = Some op_store; int_params = [] } [a; k; v]
let left = store (constant A.int_array zero) two three
let right = store (constant A.int_array one) two three
let source = mk_eq_expr left right
let target =
  let args = [mk_eq_expr three three; mk_eq_expr three three; mk_eq_expr zero one] in
  App (B.connective_decl B.Conjunction args) args

let lemma_obligation ()
  : Lemma (A.unequal_defaults source /\ N.equivalent source target)
  = assert_norm (A.unequal_defaults source /\ N.equivalent source target)

let symbol (name:string) : expr =
  App { decl_name = name; domain = []; range = int_s; interp = None; int_params = [] } []

let nested =
  mk_eq_expr (store (store left (symbol "i") one) (symbol "i") zero)
             (store right (symbol "j") (symbol "v"))

let lemma_symbolic_repeated_and_asymmetric_chains ()
  : Lemma (A.unequal_defaults nested)
  = assert_norm (A.unequal_defaults nested)

let lemma_semantics (i:interpretation value) (rho:env value)
  : Lemma (requires N.normalization_model i)
          (ensures eval i source rho == eval i target rho)
  = lemma_obligation ();
    N.lemma_equivalent i rho source target

let lemma_same_default_not_decided ()
  : Lemma (~(A.unequal_defaults (mk_eq_expr left left)) /\
           ~(N.equivalent source true_expr))
  = assert_norm (~(A.unequal_defaults (mk_eq_expr left left)) /\
                 ~(N.equivalent source true_expr))

let finite_array = ArraySort [BaseSort "BV1"] int_s
let finite = mk_eq_expr (constant finite_array zero) (constant finite_array one)
let bool_array = ArraySort [bool_sort] int_s

let lemma_finite_domains_rejected ()
  : Lemma (~(A.unequal_defaults finite) /\
           ~(A.unequal_defaults (mk_eq_expr (constant bool_array zero)
                                           (constant bool_array one))))
  = assert_norm (~(A.unequal_defaults finite) /\
                 ~(A.unequal_defaults (mk_eq_expr (constant bool_array zero)
                                                 (constant bool_array one))))

(* Exhausting a finite domain really invalidates the proposed default
   disequality inference: both different-default arrays become equal. *)
let lemma_exhausted_boolean_domain ()
  : Lemma (T.store (T.store (T.const_arr #bool #int 0) false 3) true 3 ==
           T.store (T.store (T.const_arr #bool #int 1) false 3) true 3)
  = T.lemma_array_extensionality
      (T.store (T.store (T.const_arr #bool #int 0) false 3) true 3)
      (T.store (T.store (T.const_arr #bool #int 1) false 3) true 3)

let lemma_exact_declarations_required ()
  : Lemma (forall (f:func_decl) (args:list expr).
      f.range == A.int_array /\ f.interp <> Some op_store /\ FStar.List.Tot.length args == 3 ==>
      A.default_term 64 (App f args) == None)
  = let aux (f:func_decl) (args:list expr)
      : Lemma (requires f.range == A.int_array /\ f.interp <> Some op_store /\
                        FStar.List.Tot.length args == 3)
              (ensures A.default_term 64 (App f args) == None)
      = match args with [_; _; _] -> () | _ -> () in
    FStar.Classical.forall_intro_2 (fun f args -> FStar.Classical.move_requires_2 aux f args)
