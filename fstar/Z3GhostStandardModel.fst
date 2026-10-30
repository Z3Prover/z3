(*
   Z3GhostStandardModel.fst

   A classical (ghost) standard model of the typed core contracts that
   also gives quantifiers and equality their standard meaning.

   `Z3AstTheory.interpretation` and `eval` are ghost (`GTot`), so a model
   may decide classical propositions with
   `FStar.IndefiniteDescription.strong_excluded_middle`. This module uses
   that, and nothing else, to build `ghost_standard base`, an
   interpretation over the unchanged production `Z3ValueTheory.value`
   (`VBool` keeps its ordinary `bool` payload and `VArr` its `Tot`
   function). It proves, with no hypothesis and no new axiom, that one and
   the same interpretation, with the domains `domains` and the projection
   `Z3StandardModel.std_project`, satisfies

   * `Z3CoreModel.core_model`: the typed core contracts, with the six
     canonical connective contracts, typed canonical equality, integer
     `+`/`*` and the ground bit-vector contracts;
   * the legacy, untyped `Z3ResolutionProofTheory.eq_sound`: canonical `=`
     decides the identity of ANY two values, under every environment,
     including two array values (`VArr`), which are equal exactly when
     they agree at every index (`lemma_array_equality`);
   * `typed_quantifiers`: `forall`/`exists` range over exactly the value
     lists typed for the binders (`CO.args_typed domains (L.rev bs)`,
     innermost binder first), and are true exactly when the body holds
     for all/some of them;
   * `standard_domains`: Bool is `VBool`, Int is every `VInt n` (an
     infinite domain), `BV<w>` (w <= 4096) is the `2^w` bit-vector values,
     and `(Array Int Int)` is every `VArr` array; together with
     `int_numerals`, an integer numeral `op_num_rational` with parameters
     `[n; 1]` and range Int denotes `VInt n`.

   `lemma_ghost_inhabited` packages these as one witness.

   What is NOT modeled. A lambda gets an opaque array value of its sort
   (no beta law): a ghost body cannot become the `Tot` payload of `VArr`.
   Real, datatype, finite-field, sequence and other base sorts keep the
   opaque integer carrier of `Z3StandardModel`; their quantifiers range
   over that carrier, and no claim about their standard semantics is
   made. Arrays other than those whose index sort is Int and whose element
   sort is carried by integers (for example `(Array Int Real)`, which then
   shares the `VArr` carrier) are opaque integers. Numerals other than the
   integer form above (fractions, Real range, a wrong parameter list) are
   opaque leaves, never truncated. `select`/`store` are interpreted only at
   `(Array Int Int)`.

   This is NOT a model of `Z3UnifiedProof.model_sound`: its untyped
   `boolean_model`, numeric, array and binder contracts quantify over
   arbitrary environments and are still unsatisfiable (see
   `Z3GhostStandardModelTests.ghost_boolean_model_fails` and
   `Z3ScopedModelTests`). The older witness `Z3CoreModel.witness` remains a
   core model that does not satisfy the untyped `eq_sound`
   (`Z3CoreModelTests.core_without_untyped_equality`); every core model
   need only satisfy the typed contracts.

   The interpretation is a proof object (ghost, `noextract`); nothing here
   is executable or reaches the checker.
*)
module Z3GhostStandardModel

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module C = Z3CanonicalOps
module D = Z3Definitions
module SM = Z3StandardModel
module CM = Z3Commutativity
module CO = Z3CoreModel
module A = Z3ArrayTheory
module BV = Z3BvLemma
module ID = FStar.IndefiniteDescription
module L = FStar.List.Tot

(* --- Carriers ------------------------------------------------------------- *)

let int_sort : sort = CM.int_sort
let array_sort : sort = ArraySort [int_sort] int_sort

(* The array sorts whose values are `VArr` arrays: index sort Int, and an
   element sort whose values are integers. *)
noextract let rec array_carried (s:sort) : Tot bool (decreases s) =
  match s with
  | ArraySort [d] r -> d = int_sort && r <> bool_sort && None? (SM.width_of_sort r) && not (array_carried r)
  | _ -> false

(* The values of a sort: `VArr` for the array sorts above, otherwise as in
   `Z3StandardModel.fits` (`VBool`, bit-vectors of the right width, and
   integers for every other sort). *)
noextract let gfits (s:sort) (v:value) : bool =
  if array_carried s then VArr? v else SM.fits s v

let domains : CO.domains = fun s v -> gfits s v == true

noextract let gshape (s:sort) (n:int) : value =
  if array_carried s then VArr (A.const_arr n) else SM.shape s n

noextract let gcoerce (s:sort) (v:value) : value = if gfits s v then v else gshape s 0

let lemma_gshape_fits (s:sort) (n:int) : Lemma (gfits s (gshape s n)) = SM.lemma_shape_fits s n

let lemma_gcoerce_fits (s:sort) (v:value) : Lemma (gfits s (gcoerce s v)) = lemma_gshape_fits s 0

let lemma_int_carried () : Lemma (~(array_carried int_sort) /\ int_sort <> bool_sort /\ SM.width_of_sort int_sort == None)
  = CO.lemma_int_width ()

let lemma_array_carried () : Lemma (array_carried array_sort)
  = lemma_int_carried ()

let lemma_fits_int (v:value) : Lemma (gfits int_sort v <==> VInt? v) = lemma_int_carried ()

let lemma_fits_array (v:value) : Lemma (gfits array_sort v <==> VArr? v) = lemma_array_carried ()

let lemma_fits_bool (v:value) : Lemma (gfits bool_sort v <==> VBool? v) = ()

(* --- Classical decisions -------------------------------------------------- *)

noextract let decide (p:prop) : GTot bool = ID.strong_excluded_middle p

let lemma_decide (p:prop) : Lemma (decide p == true <==> p) = ()

(* --- The interpretation --------------------------------------------------- *)

(* An integer numeral: Z3's rational numeral with denominator 1 and range Int. *)
noextract let int_numeral (f:func_decl) : option int =
  match f.int_params with
  | [n; d] -> if d = 1 && f.interp = Some op_num_rational && f.domain = [] && f.range = int_sort
              then Some n else None
  | _ -> None

noextract let select_decl (f:func_decl) : bool =
  f.interp = Some op_select && f.domain = [array_sort; int_sort] && f.range = int_sort && f.int_params = []

noextract let store_decl (f:func_decl) : bool =
  f.interp = Some op_store && f.domain = [array_sort; int_sort; int_sort] && f.range = array_sort &&
  f.int_params = []

noextract let special (f:func_decl) : bool =
  C.canonical_eq f || Some? (int_numeral f) || select_decl f || store_decl f

(* Canonical `=` decides value identity classically; integer numerals,
   `select` and `store` at (Array Int Int) are computed; every other head
   is computed as in `Z3StandardModel.standard`, with integer `+`/`*` as in
   `Z3CoreModel.witness`, and the result coerced to its range sort. *)
noextract let gapp (base:func_decl -> list value -> int) (f:func_decl) (vs:list value) : GTot value =
  let other = gcoerce f.range (SM.std_app (CO.core_leaf base) f vs) in
  if C.canonical_eq f then
    (match vs with
     | [a; b] -> VBool (decide (a == b))
     | _ -> other)
  else match int_numeral f with
  | Some n -> (match vs with [] -> VInt n | _ -> other)
  | None ->
    if select_decl f then
      (match vs with [VArr a; VInt k] -> VInt (A.select a k) | _ -> VInt 0)
    else if store_decl f then
      (match vs with [VArr a; VInt k; VInt x] -> VArr (A.store a k x) | _ -> VArr (A.const_arr 0))
    else other

(* `forall`/`exists` over the typed value lists; a lambda is an opaque
   value of its array sort (an `(Array Int s)` with `s` carried by
   integers is a `VArr`, every other array sort an integer). *)
noextract let gquant (k:quantifier_kind) (bs:list sort) (body:list value -> GTot value) : GTot value =
  match k with
  | Forall_k ->
    VBool (decide (forall (vs:list value). CO.args_typed domains (L.rev bs) vs ==> body vs == VBool true))
  | Exists_k ->
    VBool (decide (exists (vs:list value). CO.args_typed domains (L.rev bs) vs /\ body vs == VBool true))
  | Lambda_k ->
    if bs = [int_sort] && decide (forall (x:int). VInt? (body [VInt x])) then VArr (A.const_arr 0)
    else VInt 0

noextract let ghost_standard (base:func_decl -> list value -> int) : interpretation value =
  { interp_app = (fun f vs -> gapp base f vs);
    uninterp_app = (fun f vs -> gshape f.range (base f vs));
    interp_quant = gquant }

(* --- Basic facts ------------------------------------------------------------ *)

let lemma_eval_app (base:func_decl -> list value -> int) (f:func_decl) (args:list expr) (rho:env value)
  : Lemma (eval (ghost_standard base) (App f args) rho ==
           (if Some? f.interp then gapp base f (eval_args (ghost_standard base) args rho)
            else gshape f.range (base f (eval_args (ghost_standard base) args rho))))
  = ()

let lemma_gapp_fits (base:func_decl -> list value -> int) (f:func_decl) (vs:list value)
  : Lemma (gfits f.range (gapp base f vs))
  = lemma_gcoerce_fits f.range (SM.std_app (CO.core_leaf base) f vs);
    lemma_int_carried ();
    lemma_array_carried ()

let lemma_gapp_other (base:func_decl -> list value -> int) (f:func_decl) (vs:list value)
  : Lemma (requires not (special f))
          (ensures gapp base f vs == gcoerce f.range (SM.std_app (CO.core_leaf base) f vs))
  = ()

(* --- Typing ------------------------------------------------------------------ *)

let lemma_app_typed (base:func_decl -> list value -> int) (f:func_decl) (vs:list value)
  : Lemma (domains f.range (CO.applied (ghost_standard base) f vs))
  = if Some? f.interp then lemma_gapp_fits base f vs
    else lemma_gshape_fits f.range (base f vs)

let lemma_typed_int (x:int) : Lemma (CO.args_typed domains [int_sort] [VInt x])
  = lemma_fits_int (VInt x)

let lemma_lambda_typed (base:func_decl -> list value -> int) (bs:list sort) (s:sort)
                       (body:list value -> GTot value)
  : Lemma (requires forall (vs:list value). CO.args_typed domains (L.rev bs) vs ==> domains s (body vs))
          (ensures domains (ArraySort bs s) (gquant Lambda_k bs body))
  = if bs = [int_sort] then (
      assert_norm (L.rev [int_sort] == [int_sort]);
      FStar.Classical.forall_intro lemma_typed_int;
      if array_carried (ArraySort bs s) then (
        assert (forall (x:int). gfits s (body [VInt x]));
        assert (forall (x:int). VInt? (body [VInt x]))
      ) else (
        lemma_typed_int 0;
        assert (gfits s (body [VInt 0]));
        assert (~(VInt? (body [VInt 0])))
      ))

let lemma_typing (base:func_decl -> list value -> int)
  : Lemma (CO.typing (ghost_standard base) domains)
  = let i = ghost_standard base in
    FStar.Classical.forall_intro lemma_fits_bool;
    FStar.Classical.forall_intro_2 (lemma_app_typed base);
    introduce forall (bs:list sort) (s:sort) (body:list value -> GTot value).
      (forall (vs:list value). CO.args_typed domains (L.rev bs) vs ==> domains s (body vs)) ==>
      domains (ArraySort bs s) (i.interp_quant Lambda_k bs body)
    with FStar.Classical.move_requires (lemma_lambda_typed base bs s) body

(* --- Connectives and equality ------------------------------------------------ *)

let lemma_connectives (base:func_decl -> list value -> int)
  : Lemma (canonical_connectives (ghost_standard base))
  = let i = ghost_standard base in
    let conj (f:func_decl) (args:list expr) (rho:env value)
      : Lemma (C.canonical_and f ==> (eval i (App f args) rho == VBool true <==> conj_holds i rho args))
      = SM.lemma_all_true i rho args in
    let disj (f:func_decl) (args:list expr) (rho:env value)
      : Lemma (C.canonical_or f ==> (eval i (App f args) rho == VBool true <==> clause_holds i rho args))
      = SM.lemma_some_true i rho args in
    FStar.Classical.forall_intro_3 conj;
    FStar.Classical.forall_intro_3 disj

(* Canonical `=` decides the identity of any two values, under every
   environment: the legacy untyped contract. *)
let lemma_equality_app (base:func_decl -> list value -> int) (f:func_decl) (a b:expr) (rho:env value)
  : Lemma (C.canonical_eq f ==>
           eval (ghost_standard base) (App f [a; b]) rho ==
           VBool (decide (eval (ghost_standard base) a rho == eval (ghost_standard base) b rho)))
  = ()

let lemma_eq_sound (base:func_decl -> list value -> int) : Lemma (eq_sound (ghost_standard base))
  = let i = ghost_standard base in
    let aux (f:func_decl) (a b:expr) (rho:env value)
      : Lemma (C.canonical_eq f ==> (eval i (App f [a; b]) rho == VBool true <==> eval i a rho == eval i b rho))
      = lemma_equality_app base f a b rho;
        lemma_decide (eval i a rho == eval i b rho) in
    FStar.Classical.forall_intro_4 aux

let lemma_canonical_equality (base:func_decl -> list value -> int)
  : Lemma (CO.canonical_equality (ghost_standard base) domains)
  = lemma_eq_sound base

(* --- Integer arithmetic ---------------------------------------------------- *)

let lemma_arithmetic_app (base:func_decl -> list value -> int) (f:func_decl) (a b:expr) (rho:env value)
  : Lemma (CM.arithmetic_decl f ==>
           eval (ghost_standard base) (App f [a; b]) rho ==
           (match eval (ghost_standard base) a rho, eval (ghost_standard base) b rho with
            | VInt x, VInt y -> VInt (if f.interp = Some op_plus then x + y else x * y)
            | _, _ -> VInt 0))
  = if CM.arithmetic_decl f then (
      let i = ghost_standard base in
      let vs = eval_args i [a; b] rho in
      lemma_int_carried ();
      assert (vs == [eval i a rho; eval i b rho]);
      assert (not (special f));
      lemma_gapp_other base f vs;
      assert (SM.bool_raw f vs == None);
      assert (SM.bv_raw f vs == None);
      assert (SM.shape int_sort (CO.core_leaf base f vs) == VInt (CO.core_leaf base f vs));
      lemma_fits_int (VInt (CO.core_leaf base f vs)))

let lemma_arithmetic (base:func_decl -> list value -> int)
  : Lemma (CM.arithmetic_model (ghost_standard base))
  = FStar.Classical.forall_intro_4 (lemma_arithmetic_app base)

(* --- The ground bit-vector contracts ---------------------------------------- *)

let lemma_not_array_carried (s:sort)
  : Lemma (requires s == bool_sort \/ Some? (SM.width_of_sort s)) (ensures ~(array_carried s))
  = ()

let lemma_bv_head (base:func_decl -> list value -> int) (f:func_decl) (args:list expr) (rho:env value)
  : Lemma (Some? f.interp /\ (f.range == bool_sort \/ Some? (SM.width_of_sort f.range)) /\
           Some? (SM.bv_raw f (eval_args (ghost_standard base) args rho)) ==>
           eval (ghost_standard base) (App f args) rho ==
           SM.coerce f.range (Some?.v (SM.bv_raw f (eval_args (ghost_standard base) args rho))))
  = let i = ghost_standard base in
    let vs = eval_args i args rho in
    if Some? f.interp && (f.range = bool_sort || Some? (SM.width_of_sort f.range)) && Some? (SM.bv_raw f vs) then (
      lemma_not_array_carried f.range;
      SM.lemma_bv_not_boolean f vs;
      assert (not (special f));
      lemma_gapp_other base f vs;
      SM.lemma_coerce_fits f.range (Some?.v (SM.bv_raw f vs)))

let lemma_bv_fit (base:func_decl -> list value -> int) (e:expr) (rho:env value)
  : Lemma (SM.ground e /\ Some? (SM.width_of_sort (get_sort e)) ==> SM.fits (get_sort e) (eval (ghost_standard base) e rho))
  = match e with
    | App f args ->
      if Some? (SM.width_of_sort f.range) then (
        let i = ghost_standard base in
        let vs = eval_args i args rho in
        lemma_not_array_carried f.range;
        lemma_int_carried ();
        lemma_array_carried ();
        if Some? f.interp then lemma_gapp_fits base f vs
        else lemma_gshape_fits f.range (base f vs))
    | _ -> ()

let lemma_bv_like (base:func_decl -> list value -> int) : Lemma (SM.bv_like (ghost_standard base))
  = FStar.Classical.forall_intro_3 (lemma_bv_head base);
    FStar.Classical.forall_intro_2 (lemma_bv_fit base)

(* --- The typed core contracts ------------------------------------------------ *)

let lemma_core_model (base:func_decl -> list value -> int)
  : Lemma (CO.core_model (ghost_standard base) domains)
  = lemma_typing base;
    lemma_connectives base;
    lemma_canonical_equality base;
    lemma_arithmetic base;
    lemma_bv_like base;
    SM.lemma_bv_like_ground (ghost_standard base)

(* --- Typed quantifiers ------------------------------------------------------- *)

let typed_quantifiers (i:interpretation value) (dom:CO.domains) : prop =
  forall (bs:list sort) (s:sort) (body:expr) (rho:env value).
    (eval i (Quantifier Forall_k bs s body) rho == VBool true <==>
     (forall (vs:list value). CO.args_typed dom (L.rev bs) vs ==> eval i body (shift vs rho) == VBool true)) /\
    (eval i (Quantifier Exists_k bs s body) rho == VBool true <==>
     (exists (vs:list value). CO.args_typed dom (L.rev bs) vs /\ eval i body (shift vs rho) == VBool true))

let lemma_forall (base:func_decl -> list value -> int) (bs:list sort) (s:sort) (body:expr) (rho:env value)
  : Lemma (eval (ghost_standard base) (Quantifier Forall_k bs s body) rho ==
           VBool (decide (forall (vs:list value). CO.args_typed domains (L.rev bs) vs ==>
                                                 eval (ghost_standard base) body (shift vs rho) == VBool true)))
  = ()

let lemma_exists (base:func_decl -> list value -> int) (bs:list sort) (s:sort) (body:expr) (rho:env value)
  : Lemma (eval (ghost_standard base) (Quantifier Exists_k bs s body) rho ==
           VBool (decide (exists (vs:list value). CO.args_typed domains (L.rev bs) vs /\
                                                 eval (ghost_standard base) body (shift vs rho) == VBool true)))
  = ()

let lemma_typed_quantifiers (base:func_decl -> list value -> int)
  : Lemma (typed_quantifiers (ghost_standard base) domains)
  = let i = ghost_standard base in
    let aux (bs:list sort) (s:sort) (body:expr) (rho:env value)
      : Lemma ((eval i (Quantifier Forall_k bs s body) rho == VBool true <==>
                (forall (vs:list value). CO.args_typed domains (L.rev bs) vs ==> eval i body (shift vs rho) == VBool true)) /\
               (eval i (Quantifier Exists_k bs s body) rho == VBool true <==>
                (exists (vs:list value). CO.args_typed domains (L.rev bs) vs /\ eval i body (shift vs rho) == VBool true)))
      = lemma_forall base bs s body rho;
        lemma_exists base bs s body rho;
        lemma_decide (forall (vs:list value). CO.args_typed domains (L.rev bs) vs ==> eval i body (shift vs rho) == VBool true);
        lemma_decide (exists (vs:list value). CO.args_typed domains (L.rev bs) vs /\ eval i body (shift vs rho) == VBool true) in
    FStar.Classical.forall_intro_4 aux

(* --- Standard domains and integer numerals ----------------------------------- *)

let standard_domains (dom:CO.domains) : prop =
  (forall (v:value). dom bool_sort v <==> VBool? v) /\
  (forall (v:value). dom int_sort v <==> VInt? v) /\
  (forall (v:value). dom array_sort v <==> VArr? v) /\
  (forall (w:pos) (v:value). w <= SM.max_width ==>
     (dom (BV.bv_sort w) v <==> (exists (r:nat). r < pow2 w /\ v == VSeq [w; r])))

let int_numerals (i:interpretation value) : prop =
  forall (f:func_decl) (rho:env value) (n:int).
    f.interp == Some op_num_rational /\ f.domain == [] /\ f.range == int_sort /\ f.int_params == [n; 1] ==>
    eval i (App f []) rho == VInt n

let lemma_bv_domain (w:pos) (v:value)
  : Lemma (requires w <= SM.max_width)
          (ensures domains (BV.bv_sort w) v <==> (exists (r:nat). r < pow2 w /\ v == VSeq [w; r]))
  = SM.lemma_width w;
    SM.lemma_bool_width ();
    assert (~(array_carried (BV.bv_sort w)));
    match v with
    | VSeq [w'; r] -> if w' = w && 0 <= r && r < pow2 w then assert (v == VSeq [w; r])
    | _ -> ()

let lemma_standard_domains () : Lemma (standard_domains domains)
  = FStar.Classical.forall_intro lemma_fits_int;
    FStar.Classical.forall_intro lemma_fits_array;
    FStar.Classical.forall_intro lemma_fits_bool;
    introduce forall (w:pos) (v:value). w <= SM.max_width ==>
      (domains (BV.bv_sort w) v <==> (exists (r:nat). r < pow2 w /\ v == VSeq [w; r]))
    with FStar.Classical.move_requires (lemma_bv_domain w) v

let lemma_int_numerals (base:func_decl -> list value -> int) : Lemma (int_numerals (ghost_standard base))
  = lemma_int_carried ()

(* --- Extensional array equality ---------------------------------------------- *)

let lemma_array_equality (base:func_decl -> list value -> int) (f:func_decl) (a b:expr) (rho:env value)
                         (x y:A.arr int int)
  : Lemma (requires C.canonical_eq f /\ eval (ghost_standard base) a rho == VArr x /\
                    eval (ghost_standard base) b rho == VArr y)
          (ensures eval (ghost_standard base) (App f [a; b]) rho == VBool true <==>
                   (forall (k:int). A.select x k == A.select y k))
  = lemma_eq_sound base;
    A.lemma_array_extensionality x y

(* --- One witness for all of them ---------------------------------------------- *)

let ghost_model (i:interpretation value) (dom:CO.domains) : prop =
  CO.core_model i dom /\ eq_sound i /\ typed_quantifiers i dom /\ standard_domains dom /\ int_numerals i

let lemma_ghost_standard (base:func_decl -> list value -> int)
  : Lemma (ghost_model (ghost_standard base) domains /\ SM.ground_bv (ghost_standard base) SM.std_project)
  = lemma_core_model base;
    lemma_bv_like base;
    SM.lemma_bv_like_ground (ghost_standard base);
    lemma_eq_sound base;
    lemma_typed_quantifiers base;
    lemma_standard_domains ();
    lemma_int_numerals base

let lemma_ghost_inhabited ()
  : Lemma (exists (i:interpretation value) (dom:CO.domains). ghost_model i dom)
  = lemma_ghost_standard (fun _ _ -> 0)
