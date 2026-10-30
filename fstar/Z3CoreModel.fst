(*
   Z3CoreModel.fst

   Typed canonical core contracts with model-owned sort domains, and a
   hypothesis-free standard model of them.

   `Z3UnifiedProof.model_sound` has no model (`Z3ScopedModelTests`,
   `Z3CoreModelTests`): several of its conjuncts quantify over open terms
   under every environment, its quantifier and lambda contracts read
   bodies under untyped value lists, and the store clause of `array_model`
   and the numeral clauses of `numeric_operators` are already jointly
   unsatisfiable on a closed, well-sorted term (finite clause instances in
   `Z3CoreModelTests`). Its connective contracts are now keyed by
   `Z3CanonicalOps`, which removes the name/tag clashes with the
   bit-vector and datatype contracts, but not these obstructions. This
   module states a smaller contract, `core_model`, that the kernel's
   Boolean, equality and congruence rules need, and proves that it has
   models.

   * A model owns its sort domains (`domains`): the values that terms and
     variables of each sort take. `typing` fixes only `Bool`, to `VBool`,
     but the domains are not arbitrary: `arithmetic_model` makes integer
     `+`/`*` return `VInt` (`VInt 0` on non-integer arguments), so the Int
     domain must contain those images, and canonical equality must decide
     value identity wherever it is applied; under the current `Tot`
     interpretation fields no construction is known for a carrier with
     several distinct array (function) values (not proved impossible).
     Standard models choose their own carriers; the witness below is not
     baked into the contract.
   * Environments are typed against a scope of sorts (`env_typed`), the
     same de Bruijn convention as `Z3Definitions.scoped`: index 0 is the
     innermost binder. A lambda's argument list is innermost-first, so it
     is typed by `L.rev bs`.
   * `lemma_typed_eval`: every term scoped in `scope` takes a value of its
     sort under every environment typed for `scope`. This covers open
     terms and binders.
   * The connectives are keyed only by the typed canonical predicates of
     `Z3CanonicalOps` (`Z3ResolutionProofTheory.canonical_connectives`).
     Equality is canonical and typed: it is required to decide value
     identity only on scoped terms under typed environments.
   * `Z3Commutativity.arithmetic_model` (integer `+`/`*`) and the ground
     bit-vector contracts of `Z3StandardModel` are included.

   The witness is `Z3StandardModel.standard` with integer `+`/`*`
   computed, and `Z3StandardModel.fits` as its domains.
   `lemma_core_inhabited` proves `exists i dom. core_model i dom`.

   This is NOT a model of `model_sound`. Quantifier truth, lambda/array
   semantics, real arithmetic, datatypes and finite fields are not
   constrained by `core_model`: the witness gives `forall`/`exists` a
   constant value and lambdas an opaque one. For a standard semantics of
   quantifiers over infinite domains, and of equality between array
   values, no construction is known under the current `Tot`
   interpretation fields (it would need classical decisions); this is
   not proved impossible.
*)
module Z3CoreModel

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module C = Z3CanonicalOps
module D = Z3Definitions
module SM = Z3StandardModel
module CM = Z3Commutativity
module DV = Z3DatatypeValue
module L = FStar.List.Tot

(* --- Typed environments ---------------------------------------------- *)

type domains = sort -> value -> prop

let rec args_typed (dom:domains) (ss:list sort) (vs:list value) : Tot prop (decreases ss) =
  match ss, vs with
  | [], [] -> True
  | s :: rest, v :: tail -> dom s v /\ args_typed dom rest tail
  | _, _ -> False

let env_typed (dom:domains) (scope:list sort) (rho:env value) : prop =
  forall (n:nat). n < L.length scope ==> dom (L.index scope n) (rho n)

let applied (i:interpretation value) (f:func_decl) (vs:list value) : value =
  if Some? f.interp then i.interp_app f vs else i.uninterp_app f vs

let typing (i:interpretation value) (dom:domains) : prop =
  (forall (v:value). dom bool_sort v <==> VBool? v) /\
  (forall (f:func_decl) (vs:list value). args_typed dom f.domain vs ==> dom f.range (applied i f vs)) /\
  (forall (k:quantifier_kind) (bs:list sort) (body:list value -> value).
     (k = Forall_k \/ k = Exists_k) ==> VBool? (i.interp_quant k bs body)) /\
  (forall (bs:list sort) (s:sort) (body:list value -> value).
     (forall (vs:list value). args_typed dom (L.rev bs) vs ==> dom s (body vs)) ==>
     dom (ArraySort bs s) (i.interp_quant Lambda_k bs body))

let rec lemma_args_typed_length (dom:domains) (ss:list sort) (vs:list value)
  : Lemma (requires args_typed dom ss vs) (ensures L.length vs == L.length ss) (decreases ss)
  = match ss, vs with
    | _ :: rest, _ :: tail -> lemma_args_typed_length dom rest tail
    | _, _ -> ()

let rec lemma_args_typed_index (dom:domains) (ss:list sort) (vs:list value) (n:nat)
  : Lemma (requires args_typed dom ss vs /\ n < L.length ss)
          (ensures n < L.length vs /\ dom (L.index ss n) (L.index vs n)) (decreases ss)
  = match ss, vs with
    | _ :: rest, _ :: tail -> if n = 0 then () else lemma_args_typed_index dom rest tail (n - 1)
    | _, _ -> ()

let rec lemma_index_append (ss scope:list sort) (n:nat)
  : Lemma (requires n < L.length ss + L.length scope)
          (ensures L.length (L.append ss scope) == L.length ss + L.length scope /\
                   L.index (L.append ss scope) n ==
                   (if n < L.length ss then L.index ss n else L.index scope (n - L.length ss)))
          (decreases ss)
  = FStar.List.Tot.Properties.append_length ss scope;
    match ss with
    | [] -> ()
    | _ :: rest -> if n = 0 then () else lemma_index_append rest scope (n - 1)

let lemma_env_shift (dom:domains) (ss scope:list sort) (vs:list value) (rho:env value)
  : Lemma (requires args_typed dom ss vs /\ env_typed dom scope rho)
          (ensures env_typed dom (L.append ss scope) (shift vs rho))
  = lemma_args_typed_length dom ss vs;
    FStar.List.Tot.Properties.append_length ss scope;
    let aux (n:nat)
      : Lemma (n < L.length (L.append ss scope) ==>
               dom (L.index (L.append ss scope) n) (shift vs rho n))
      = if n < L.length (L.append ss scope) then (
          lemma_index_append ss scope n;
          if n < L.length ss then lemma_args_typed_index dom ss vs n) in
    FStar.Classical.forall_intro aux

let lemma_env_closed (dom:domains) (rho:env value) : Lemma (env_typed dom [] rho) = ()

(* Every scoped term, under a typed environment, takes a value of its sort. *)
let rec lemma_typed_eval (i:interpretation value) (dom:domains) (scope:list sort) (e:expr) (rho:env value)
  : Lemma (requires typing i dom /\ D.scoped scope e /\ env_typed dom scope rho)
          (ensures dom (get_sort e) (eval i e rho))
          (decreases e)
  = match e with
    | Var _ _ -> ()
    | App f args ->
      lemma_typed_args i dom scope args f.domain rho;
      assert (eval i e rho == applied i f (eval_args i args rho))
    | Quantifier k bs s body ->
      if k = Lambda_k then (
        let aux (vs:list value)
          : Lemma (requires args_typed dom (L.rev bs) vs)
                  (ensures dom (get_sort body) (eval i body (shift vs rho)))
          = lemma_env_shift dom (L.rev bs) scope vs rho;
            lemma_typed_eval i dom (L.append (L.rev bs) scope) body (shift vs rho) in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux))
      else assert (VBool? (eval i e rho))

and lemma_typed_args (i:interpretation value) (dom:domains) (scope:list sort)
                     (args:list expr) (ss:list sort) (rho:env value)
  : Lemma (requires typing i dom /\ D.scoped_args scope args /\ sorts_match args ss /\
                    env_typed dom scope rho)
          (ensures args_typed dom ss (eval_args i args rho))
          (decreases args)
  = match args, ss with
    | a :: rest, s :: tail ->
      lemma_typed_eval i dom scope a rho;
      DV.lemma_sort_eq (get_sort a) s;
      lemma_typed_args i dom scope rest tail rho
    | _, _ -> ()

let lemma_typed_bool (i:interpretation value) (dom:domains) (scope:list sort) (e:expr) (rho:env value)
  : Lemma (requires typing i dom /\ D.scoped scope e /\ env_typed dom scope rho /\ get_sort e == bool_sort)
          (ensures VBool? (eval i e rho))
  = lemma_typed_eval i dom scope e rho

(* --- The core contracts ------------------------------------------------- *)

let canonical_equality (i:interpretation value) (dom:domains) : prop =
  forall (scope:list sort) (f:func_decl) (a b:expr) (rho:env value).
    {:pattern (eval i (App f [a; b]) rho); D.scoped scope (App f [a; b])}
    C.canonical_eq f /\ D.scoped scope (App f [a; b]) /\ env_typed dom scope rho ==>
    (eval i (App f [a; b]) rho == VBool true <==> eval i a rho == eval i b rho)

let core_model (i:interpretation value) (dom:domains) : prop =
  typing i dom /\ canonical_connectives i /\ canonical_equality i dom /\
  CM.arithmetic_model i /\
  (exists (project:pos -> value -> int). SM.ground_bv i project)

let lemma_equality (i:interpretation value) (dom:domains) (scope:list sort)
                   (f:func_decl) (a b:expr) (rho:env value)
  : Lemma (requires core_model i dom /\ C.canonical_eq f /\ D.scoped scope (App f [a; b]) /\
                    env_typed dom scope rho)
          (ensures eval i (App f [a; b]) rho == VBool true <==> eval i a rho == eval i b rho)
  = ()

(* `mk_eq_expr a b` is scoped exactly when `a` and `b` are scoped with one sort. *)
let lemma_eq_scoped (scope:list sort) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == get_sort b)
          (ensures D.scoped scope (mk_eq_expr a b) /\ C.canonical_eq (eq_decl (get_sort a)))
  = DV.lemma_sort_eq (get_sort a) (get_sort a)

let lemma_eq_expr (i:interpretation value) (dom:domains) (scope:list sort) (a b:expr) (rho:env value)
  : Lemma (requires core_model i dom /\ D.scoped scope a /\ D.scoped scope b /\
                    get_sort a == get_sort b /\ env_typed dom scope rho)
          (ensures lit_true i rho (mk_eq_expr a b) <==> eval i a rho == eval i b rho)
  = lemma_eq_scoped scope a b;
    lemma_equality i dom scope (eq_decl (get_sort a)) a b rho

(* The core contracts contain the ground Boolean and bit-vector contracts. *)
let lemma_ground_boolean (i:interpretation value) (dom:domains)
  : Lemma (requires core_model i dom) (ensures SM.ground_boolean i)
  = let typed (a:expr) (rho:env value)
      : Lemma (SM.closed_ground a /\ get_sort a == bool_sort ==> VBool? (eval i a rho))
      = if SM.closed_ground a && get_sort a = bool_sort then lemma_typed_bool i dom [] a rho in
    let equal (f:func_decl) (a b:expr) (rho:env value)
      : Lemma (C.canonical_eq f /\ SM.closed_ground (App f [a; b]) ==>
               (eval i (App f [a; b]) rho == VBool true <==> eval i a rho == eval i b rho))
      = if C.canonical_eq f && SM.closed_ground (App f [a; b]) then lemma_equality i dom [] f a b rho in
    FStar.Classical.forall_intro_2 typed;
    FStar.Classical.forall_intro_4 equal

let lemma_ground_model (i:interpretation value) (dom:domains)
  : Lemma (requires core_model i dom)
          (ensures exists (project:pos -> value -> int). SM.ground_model i project)
  = lemma_ground_boolean i dom

(* --- The witness ------------------------------------------------------- *)

(* Integer `+` and `*` are computed; every other opaque head uses `base`. *)
noextract let core_leaf (base:func_decl -> list value -> int) (f:func_decl) (vs:list value) : int =
  if CM.arithmetic_decl f then
    (match vs with
     | [VInt x; VInt y] -> if f.interp = Some op_plus then x + y else x * y
     | _ -> 0)
  else base f vs

noextract let witness (base:func_decl -> list value -> int) : interpretation value =
  SM.standard (core_leaf base)

let witness_domains : domains = fun s v -> SM.fits s v == true

let lemma_witness_fits (base:func_decl -> list value -> int) (f:func_decl) (vs:list value)
  : Lemma (SM.fits f.range (applied (witness base) f vs))
  = let leaf = core_leaf base in
    SM.lemma_shape_fits f.range (leaf f vs);
    (match SM.bool_raw f vs with
     | Some v -> SM.lemma_coerce_fits f.range v
     | None -> (match SM.bv_raw f vs with Some v -> SM.lemma_coerce_fits f.range v | None -> ()))

let lemma_array_fits (bs:list sort) (s:sort) : Lemma (SM.fits (ArraySort bs s) (VInt 0)) = ()

let lemma_witness_typing (base:func_decl -> list value -> int)
  : Lemma (typing (witness base) witness_domains)
  = FStar.Classical.forall_intro_2 (lemma_witness_fits base);
    FStar.Classical.forall_intro_2 lemma_array_fits

let lemma_witness_connectives (base:func_decl -> list value -> int)
  : Lemma (canonical_connectives (witness base))
  = let i = witness base in
    let conj (f:func_decl) (args:list expr) (rho:env value)
      : Lemma (C.canonical_and f ==> (eval i (App f args) rho == VBool true <==> conj_holds i rho args))
      = SM.lemma_all_true i rho args in
    let disj (f:func_decl) (args:list expr) (rho:env value)
      : Lemma (C.canonical_or f ==> (eval i (App f args) rho == VBool true <==> clause_holds i rho args))
      = SM.lemma_some_true i rho args in
    FStar.Classical.forall_intro_3 conj;
    FStar.Classical.forall_intro_3 disj

let lemma_witness_equality (base:func_decl -> list value -> int) (scope:list sort) (f:func_decl)
                           (a b:expr) (rho:env value)
  : Lemma (C.canonical_eq f /\ D.scoped scope (App f [a; b]) /\ env_typed witness_domains scope rho ==>
           (eval (witness base) (App f [a; b]) rho == VBool true <==>
            eval (witness base) a rho == eval (witness base) b rho))
  = let i = witness base in
    if C.canonical_eq f && D.scoped scope (App f [a; b]) then
      FStar.Classical.impl_intro (fun (_:squash (env_typed witness_domains scope rho)) ->
        lemma_witness_typing base;
        lemma_typed_eval i witness_domains scope a rho;
        lemma_typed_eval i witness_domains scope b rho;
        SM.lemma_fits_scalar (get_sort a) (eval i a rho);
        SM.lemma_fits_scalar (get_sort b) (eval i b rho);
        SM.lemma_value_eq (eval i a rho) (eval i b rho))

let lemma_int_width () : Lemma (SM.width_of_sort CM.int_sort == None)
  = assert_norm (SM.width_of_sort CM.int_sort == None)

let lemma_witness_arithmetic_app (base:func_decl -> list value -> int) (f:func_decl) (a b:expr) (rho:env value)
  : Lemma (CM.arithmetic_decl f ==>
           eval (witness base) (App f [a; b]) rho ==
           (match eval (witness base) a rho, eval (witness base) b rho with
            | VInt x, VInt y -> VInt (if f.interp = Some op_plus then x + y else x * y)
            | _, _ -> VInt 0))
  = if CM.arithmetic_decl f then (
      let i = witness base in
      let vs = eval_args i [a; b] rho in
      lemma_int_width ();
      assert (vs == [eval i a rho; eval i b rho]);
      assert (f.range == CM.int_sort /\ CM.int_sort <> bool_sort);
      assert (SM.bool_raw f vs == None);
      assert (SM.bv_raw f vs == None);
      assert (SM.shape CM.int_sort (core_leaf base f vs) == VInt (core_leaf base f vs)))

let lemma_witness_arithmetic (base:func_decl -> list value -> int)
  : Lemma (CM.arithmetic_model (witness base))
  = FStar.Classical.forall_intro_4 (lemma_witness_arithmetic_app base)

let lemma_witness (base:func_decl -> list value -> int)
  : Lemma (core_model (witness base) witness_domains)
  = lemma_witness_typing base;
    lemma_witness_connectives base;
    lemma_witness_arithmetic base;
    SM.lemma_ground_bv (core_leaf base);
    introduce forall (scope:list sort) (f:func_decl) (a b:expr) (rho:env value).
      (C.canonical_eq f /\ D.scoped scope (App f [a; b]) /\ env_typed witness_domains scope rho ==>
       (eval (witness base) (App f [a; b]) rho == VBool true <==>
        eval (witness base) a rho == eval (witness base) b rho))
    with lemma_witness_equality base scope f a b rho

let lemma_core_inhabited ()
  : Lemma (exists (i:interpretation value) (dom:domains). core_model i dom)
  = lemma_witness (fun _ _ -> 0)
