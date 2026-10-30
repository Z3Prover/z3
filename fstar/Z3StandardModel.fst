(*
   Z3StandardModel.fst

   A standard model of the ground Boolean and bit-vector contracts, and
   the contracts themselves.

   The global hypothesis `Z3UnifiedProof.model_sound` has no model.
   `Z3ScopedModelTests` proves the impossible open-environment typing
   assumptions; the separate repair evidence also records the name/tag
   clashes, which keying the connective contracts by `Z3CanonicalOps`
   has since removed. Some contracts still constrain open terms under
   every environment (see `Z3CoreModel` for the typed contract the core
   kernel theorem uses). This module states smaller contracts, `ground_model`, and
   proves that they have models. It does not repair the global hypothesis.

   * The terms are closed ground terms: applications only, with no
     variable and no binder, whose arguments match their declarations'
     domains (`closed_ground`).
   * The connectives `true`, `false`, `not`, `and`, `or`, `=>` and `=` are
     keyed by the typed canonical predicates of `Z3CanonicalOps` (name,
     kind tag, domain, range and parameters).
   * The bit-vector conjuncts are the ten conjuncts of `Z3BvLemma.bv_model`,
     restricted to closed ground terms. The first conjunct (projection
     range and injectivity) is further restricted to widths of at most
     4096, the bound that every bit-vector recognizer already imposes.
     Above that bound the sort `BV<w>` cannot be decoded, because F*
     cannot prove `string_of_int` injective in general.

   `standard leaf` is an interpretation for every function `leaf`. A
   bit-vector of width `w` and residue `r` is the value `VSeq [w; r]`, so
   values of different widths are distinct. Booleans are `VBool`.
   Equality is decided on values. The witness computes canonical
   connectives and BV-tagged heads when their parameter shapes match.
   This includes BV-tagged heads outside the checker's recognizers;
   malformed results are coerced to the declaration's range sort.
   Heads outside those cases use `leaf f (argument values)`, also coerced
   to their range sort. `lemma_standard_model` proves
   `ground_model (standard leaf) std_project` for every `leaf`.
   `lemma_opaque_constant` shows that one nullary uninterpreted BV
   constant can take any residue of its bounded width. It is not a
   general independence theorem for arbitrary opaque applications.

   This is NOT a model of `model_sound`. Quantifiers, arrays, arithmetic,
   datatypes, finite fields and open terms are outside the fragment.
   Their theory laws are not asserted by the ground contracts.

   The checker uses only `ground`, `closed_ground` and `max_width` from
   here. The interpretation is a proof object and is not extracted
   (`noextract`). *)
module Z3StandardModel

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module C = Z3CanonicalOps
module D = Z3Definitions
module BV = Z3BvLemma
module BR = Z3BooleanRewrite
module L = FStar.List.Tot
module U = FStar.UInt
module M = FStar.Math.Lemmas

(* --- The fragment ------------------------------------------------------ *)

let rec ground (e:expr) : Tot bool (decreases e) =
  match e with
  | App _ args -> ground_args args
  | _ -> false

and ground_args (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest -> ground a && ground_args rest

let closed_ground (e:expr) : bool = ground e && D.scoped [] e

let max_width : pos = 4096

let ground_boolean (i:interpretation value) : prop =
  (forall (a:expr) (rho:env value).
    closed_ground a /\ get_sort a == bool_sort ==> VBool? (eval i a rho)) /\
  (forall (f:func_decl) (rho:env value).
    {:pattern (eval i (App f []) rho)}
    C.canonical_true f ==> eval i (App f []) rho == VBool true) /\
  (forall (f:func_decl) (rho:env value).
    {:pattern (eval i (App f []) rho)}
    C.canonical_false f ==> eval i (App f []) rho == VBool false) /\
  (forall (f:func_decl) (a:expr) (rho:env value).
    {:pattern (eval i (App f [a]) rho)}
    C.canonical_not f /\ closed_ground (App f [a]) ==>
    ((eval i (App f [a]) rho == VBool true) == (eval i a rho == VBool false))) /\
  (forall (f:func_decl) (args:list expr) (rho:env value).
    {:pattern (eval i (App f args) rho)}
    C.canonical_and f /\ closed_ground (App f args) ==>
    (eval i (App f args) rho == VBool true <==> conj_holds i rho args)) /\
  (forall (f:func_decl) (args:list expr) (rho:env value).
    {:pattern (eval i (App f args) rho)}
    C.canonical_or f /\ closed_ground (App f args) ==>
    (eval i (App f args) rho == VBool true <==> clause_holds i rho args)) /\
  (forall (f:func_decl) (a b:expr) (rho:env value).
    {:pattern (eval i (App f [a; b]) rho)}
    C.canonical_implies f /\ closed_ground (App f [a; b]) ==>
    (eval i (App f [a; b]) rho == VBool true <==> (lit_true i rho a ==> lit_true i rho b))) /\
  (forall (f:func_decl) (a b:expr) (rho:env value).
    {:pattern (eval i (App f [a; b]) rho)}
    C.canonical_eq f /\ closed_ground (App f [a; b]) ==>
    (eval i (App f [a; b]) rho == VBool true <==> eval i a rho == eval i b rho))

(* The ten conjuncts of `Z3BvLemma.bv_model`, on closed ground terms. *)
let bv_values (i:interpretation value) (project:pos -> value -> int) : prop =
  forall (width:pos) (a b:expr) (rho:env value).
    width <= max_width /\ closed_ground a /\ closed_ground b /\
    get_sort a == BV.bv_sort width /\ get_sort b == BV.bv_sort width ==>
    ((eval i a rho == eval i b rho <==> project width (eval i a rho) == project width (eval i b rho)) /\
     0 <= project width (eval i a rho) /\ project width (eval i a rho) < pow2 width)

let bv_numerals (i:interpretation value) (project:pos -> value -> int) : prop =
  forall (e:expr) (rho:env value) (width:pos) (n:int).
    BV.numeral e == Some (width, n) ==> project width (eval i e rho) == n

let bv_operations (i:interpretation value) (project:pos -> value -> int) : prop =
  forall (f:func_decl) (args:list expr) (rho:env value) (width:pos) (op:decl_kind).
    closed_ground (App f args) /\ BV.operation f args == Some (width, op) ==>
    project width (eval i (App f args) rho) ==
    BV.calculate width op (BV.words width project (eval_args i args rho))

let bv_nary_operations (i:interpretation value) (project:pos -> value -> int) : prop =
  forall (f:func_decl) (args:list expr) (rho:env value) (width:pos) (op:decl_kind).
    closed_ground (App f args) /\ BV.nary_operation f args == Some (width, op) ==>
    project width (eval i (App f args) rho) ==
    BV.calculate_nary width op (BV.words width project (eval_args i args rho))

let bv_extracts (i:interpretation value) (project:pos -> value -> int) : prop =
  forall (e:expr) (rho:env value) (s:BV.extraction).
    closed_ground e /\ BV.extract_parts e == Some s ==>
    project (s.BV.high - s.BV.low + 1) (eval i e rho) ==
      (project s.BV.source_width (eval i s.BV.operand rho) / pow2 s.BV.low) %
      pow2 (s.BV.high - s.BV.low + 1)

let bv_concats (i:interpretation value) (project:pos -> value -> int) : prop =
  forall (e:expr) (rho:env value) (c:BV.concatenation).
    closed_ground e /\ BV.concat_parts e == Some c ==>
    project (c.BV.left_width + c.BV.right_width) (eval i e rho) ==
      project c.BV.left_width (eval i c.BV.left rho) * pow2 c.BV.right_width +
      project c.BV.right_width (eval i c.BV.right rho)

let bv_zero_extends (i:interpretation value) (project:pos -> value -> int) : prop =
  forall (e:expr) (rho:env value) (s:BV.zero_extension).
    closed_ground e /\ BV.zero_extend_parts e == Some s ==>
    project (s.BV.input_width + s.BV.extra_width) (eval i e rho) ==
      project s.BV.input_width (eval i s.BV.argument rho)

let bv_words (i:interpretation value) (project:pos -> value -> int) : prop =
  forall (e:expr) (rho:env value) (width:pos) (args:list expr).
    closed_ground e /\ BV.word_parts e == Some (width, args) ==>
    project width (eval i e rho) == BV.bits_number (BV.bit_values i rho args)

let bv_unsigned (i:interpretation value) (project:pos -> value -> int) : prop =
  forall (e:expr) (rho:env value) (c:BV.unsigned_comparison).
    closed_ground e /\ BV.unsigned_parts e == Some c ==>
    eval i e rho == VBool (BV.unsigned_value c.BV.relation
      (project c.BV.width (eval i c.BV.lhs rho)) (project c.BV.width (eval i c.BV.rhs rho)))

let concat3_at (i:interpretation value) (project:pos -> value -> int)
               (e:expr) (rho:env value) (c:BV.concatenation3) : prop =
  closed_ground e /\ BV.concat3_parts e == Some c ==>
  project (c.BV.width1 + c.BV.width2 + c.BV.width3) (eval i e rho) ==
    project c.BV.width1 (eval i c.BV.first rho) * pow2 (c.BV.width2 + c.BV.width3) +
    project c.BV.width2 (eval i c.BV.second rho) * pow2 c.BV.width3 +
    project c.BV.width3 (eval i c.BV.third rho)

let bv_concats3 (i:interpretation value) (project:pos -> value -> int) : prop =
  forall (e:expr) (rho:env value) (c:BV.concatenation3). concat3_at i project e rho c

let ground_bv (i:interpretation value) (project:pos -> value -> int) : prop =
  bv_values i project /\ bv_numerals i project /\ bv_operations i project /\
  bv_nary_operations i project /\ bv_extracts i project /\ bv_concats i project /\
  bv_zero_extends i project /\ bv_words i project /\ bv_unsigned i project /\
  bv_concats3 i project

let ground_model (i:interpretation value) (project:pos -> value -> int) : prop =
  ground_boolean i /\ ground_bv i project

(* --- Decoding the width of a bit-vector sort --------------------------- *)

noextract let digit (c:FStar.Char.char) : option nat =
  if c = '0' then Some 0 else if c = '1' then Some 1 else if c = '2' then Some 2
  else if c = '3' then Some 3 else if c = '4' then Some 4 else if c = '5' then Some 5
  else if c = '6' then Some 6 else if c = '7' then Some 7 else if c = '8' then Some 8
  else if c = '9' then Some 9 else None

noextract let rec decimal (acc:nat) (cs:list FStar.Char.char) : Tot (option nat) (decreases cs) =
  match cs with
  | [] -> Some acc
  | c :: rest -> (match digit c with Some d -> decimal (10 * acc + d) rest | None -> None)

noextract let width_of_name (cs:list FStar.Char.char) : option pos =
  match cs with
  | 'B' :: 'V' :: d :: rest ->
    if d = '0' then None
    else (match decimal 0 (d :: rest) with
          | Some w -> if w > 0 && w <= max_width then Some w else None
          | None -> None)
  | _ -> None

noextract let width_of_sort (s:sort) : option pos =
  match s with
  | BaseSort name -> width_of_name (FStar.String.list_of_string name)
  | _ -> None

noextract let rec decoded (n:nat) : Tot bool (decreases n) =
  if n = 0 then true else width_of_sort (BV.bv_sort n) = Some n && decoded (n - 1)

(* Checked by evaluation, once for each of the 4096 widths. *)
let lemma_decoded_all () : Lemma (decoded max_width) = assert_norm (decoded max_width)

let rec lemma_decoded (n:nat) (w:pos)
  : Lemma (requires decoded n /\ w <= n) (ensures width_of_sort (BV.bv_sort w) == Some w)
          (decreases n)
  = if w = n then () else lemma_decoded (n - 1) w

let lemma_width (w:pos)
  : Lemma (requires w <= max_width) (ensures width_of_sort (BV.bv_sort w) == Some w)
  = lemma_decoded_all ();
    lemma_decoded max_width w

let lemma_bool_width () : Lemma (width_of_sort bool_sort == None)
  = assert_norm (width_of_sort bool_sort == None)

(* --- Values ---------------------------------------------------------- *)

noextract let bvv (w:pos) (r:int) : value = VSeq [w; r % pow2 w]

noextract let std_project (w:pos) (v:value) : int =
  match v with
  | VSeq [w'; r] -> if w' = w && 0 <= r && r < pow2 w then r else 0
  | _ -> 0

let lemma_std_project (w:pos) (v:value)
  : Lemma (0 <= std_project w v /\ std_project w v < pow2 w)
  = ()

let lemma_bvv (w:pos) (r:int)
  : Lemma (requires 0 <= r /\ r < pow2 w) (ensures std_project w (bvv w r) == r /\ bvv w r == VSeq [w; r])
  = M.small_mod r (pow2 w)

(* The values of a sort: a `VBool` for `Bool`, a bit-vector of the right
   width for `BV<w>` with w <= 4096, and an integer for every other sort. *)
noextract let fits (s:sort) (v:value) : bool =
  if s = bool_sort then VBool? v
  else match width_of_sort s with
       | Some w -> (match v with VSeq [w'; r] -> w' = w && 0 <= r && r < pow2 w | _ -> false)
       | None -> VInt? v

noextract let shape (s:sort) (n:int) : value =
  if s = bool_sort then VBool (n % 2 = 1)
  else match width_of_sort s with
       | Some w -> bvv w n
       | None -> VInt n

noextract let coerce (s:sort) (v:value) : value = if fits s v then v else shape s 0

let lemma_shape_fits (s:sort) (n:int) : Lemma (fits s (shape s n)) = ()

let lemma_coerce_fits (s:sort) (v:value) : Lemma (fits s (coerce s v)) = lemma_shape_fits s 0

let lemma_fits_bv (w:pos) (v:value)
  : Lemma (requires w <= max_width /\ fits (BV.bv_sort w) v)
          (ensures v == VSeq [w; std_project w v])
  = lemma_width w;
    lemma_bool_width ();
    assert (BV.bv_sort w <> bool_sort);
    match v with
    | VSeq [w'; r] -> assert (w' = w /\ 0 <= r /\ r < pow2 w)
    | _ -> ()

let lemma_fits_bool (v:value) : Lemma (requires fits bool_sort v) (ensures VBool? v) = ()

(* Equality is decidable on every value except the arrays, and no term of
   the fragment evaluates to an array. *)
noextract let value_eq (v1 v2:value) : bool =
  match v1, v2 with
  | VInt a, VInt b -> a = b
  | VBool a, VBool b -> a = b
  | VSeq a, VSeq b -> a = b
  | VBV a, VBV b -> a = b
  | _, _ -> false

let lemma_value_eq (v1 v2:value)
  : Lemma (requires ~(VArr? v1) /\ ~(VArr? v2)) (ensures value_eq v1 v2 <==> v1 == v2)
  = ()

let lemma_fits_scalar (s:sort) (v:value) : Lemma (requires fits s v) (ensures ~(VArr? v)) = ()

(* --- The standard interpretation -------------------------------------- *)

noextract let is_true (v:value) : bool = match v with VBool b -> b | _ -> false
noextract let is_false (v:value) : bool = match v with VBool b -> not b | _ -> false

noextract let rec all_true (vs:list value) : Tot bool (decreases vs) =
  match vs with
  | [] -> true
  | v :: rest -> is_true v && all_true rest

noextract let rec some_true (vs:list value) : Tot bool (decreases vs) =
  match vs with
  | [] -> false
  | v :: rest -> is_true v || some_true rest

noextract let bool_raw (f:func_decl) (vs:list value) : option value =
  if C.canonical_true f then Some (VBool true)
  else if C.canonical_false f then Some (VBool false)
  else if C.canonical_not f then (match vs with [v] -> Some (VBool (is_false v)) | _ -> None)
  else if C.canonical_and f then Some (VBool (all_true vs))
  else if C.canonical_or f then Some (VBool (some_true vs))
  else if C.canonical_implies f then
    (match vs with [a; b] -> Some (VBool (not (is_true a) || is_true b)) | _ -> None)
  else if C.canonical_eq f then (match vs with [a; b] -> Some (VBool (value_eq a b)) | _ -> None)
  else None

noextract let operation_kind (op:decl_kind) : bool =
  op = BV.op_not || op = BV.op_neg || op = BV.op_and || op = BV.op_or || op = BV.op_xor ||
  op = BV.op_add || op = BV.op_mul || op = BV.op_sub || op = BV.op_udiv || op = BV.op_urem ||
  op = BV.op_shl || op = BV.op_lshr

noextract let unsigned_kind (op:decl_kind) : bool = op = BV.op_ult || op = BV.op_ule || op = BV.op_uge

noextract let bv_raw (f:func_decl) (vs:list value) : option value =
  match f.interp with
  | None -> None
  | Some op ->
    if op = BV.op_numeral then
      (match f.int_params, vs with
       | [w; n], [] -> if w > 0 then Some (bvv w n) else None
       | _, _ -> None)
    else if operation_kind op then
      (match f.int_params with
       | [w] ->
         if w > 0 then
           (if (op = BV.op_add || op = BV.op_mul) && L.length vs >= 3
            then Some (bvv w (BV.calculate_nary w op (BV.words w std_project vs)))
            else Some (bvv w (BV.calculate w op (BV.words w std_project vs))))
         else None
       | _ -> None)
    else if op = BV.op_extract then
      (match f.int_params, vs with
       | [w; h; l], [x] ->
         if w > 0 && l >= 0 && h >= l
         then Some (bvv (h - l + 1) ((std_project w x / pow2 l) % pow2 (h - l + 1)))
         else None
       | _, _ -> None)
    else if op = BV.op_concat then
      (match f.int_params, vs with
       | [m; n], [x; y] ->
         if m > 0 && n > 0 then Some (bvv (m + n) (std_project m x * pow2 n + std_project n y)) else None
       | [a; b; c], [x; y; z] ->
         if a > 0 && b > 0 && c > 0
         then Some (bvv (a + b + c) (std_project a x * pow2 (b + c) + std_project b y * pow2 c +
                                     std_project c z))
         else None
       | _, _ -> None)
    else if op = BV.op_zero_extend then
      (match f.int_params, vs with
       | [w; k], [x] -> if w > 0 && k >= 0 then Some (bvv (w + k) (std_project w x)) else None
       | _, _ -> None)
    else if op = BV.op_mkbv then
      (match f.int_params with
       | [w] -> if w > 0 then Some (bvv w (BV.bits_number (L.map BR.bool_value vs))) else None
       | _ -> None)
    else if unsigned_kind op then
      (match f.int_params, vs with
       | [w], [x; y] ->
         if w > 0 then Some (VBool (BV.unsigned_value op (std_project w x) (std_project w y))) else None
       | _, _ -> None)
    else None

noextract let std_app (leaf:func_decl -> list value -> int) (f:func_decl) (vs:list value) : value =
  match bool_raw f vs with
  | Some v -> coerce f.range v
  | None ->
    (match bv_raw f vs with
     | Some v -> coerce f.range v
     | None -> shape f.range (leaf f vs))

(* Quantifiers are outside the ground fragment. `forall`/`exists` get the
   constant `VBool true` and a lambda the opaque `VInt 0`, so every
   binder takes a value of its sort (`Z3CoreModel.lemma_witness`); no
   quantifier or lambda law is claimed for them. *)
noextract let standard (leaf:func_decl -> list value -> int) : interpretation value =
  { interp_app = (fun f vs -> std_app leaf f vs);
    uninterp_app = (fun f vs -> shape f.range (leaf f vs));
    interp_quant = (fun k _ _ -> if k = Lambda_k then VInt 0 else VBool true) }

(* --- Basic facts about the standard interpretation --------------------- *)

let lemma_eval_app (leaf:func_decl -> list value -> int) (f:func_decl) (args:list expr) (rho:env value)
  : Lemma (eval (standard leaf) (App f args) rho ==
           (if Some? f.interp then std_app leaf f (eval_args (standard leaf) args rho)
            else shape f.range (leaf f (eval_args (standard leaf) args rho))))
  = ()

let lemma_app_fits (leaf:func_decl -> list value -> int) (f:func_decl) (args:list expr) (rho:env value)
  : Lemma (fits f.range (eval (standard leaf) (App f args) rho))
  = let vs = eval_args (standard leaf) args rho in
    lemma_shape_fits f.range (leaf f vs);
    (match bool_raw f vs with
     | Some v -> lemma_coerce_fits f.range v
     | None -> (match bv_raw f vs with Some v -> lemma_coerce_fits f.range v | None -> ()))

let lemma_ground_fits (leaf:func_decl -> list value -> int) (e:expr) (rho:env value)
  : Lemma (requires ground e) (ensures fits (get_sort e) (eval (standard leaf) e rho))
  = match e with App f args -> lemma_app_fits leaf f args rho

let rec lemma_eval_args_length (i:interpretation value) (args:list expr) (rho:env value)
  : Lemma (ensures L.length (eval_args i args rho) == L.length args) (decreases args)
  = match args with
    | [] -> ()
    | _ :: rest -> lemma_eval_args_length i rest rho

let rec lemma_all_true (i:interpretation value) (rho:env value) (args:list expr)
  : Lemma (ensures all_true (eval_args i args rho) <==> conj_holds i rho args) (decreases args)
  = match args with
    | [] -> ()
    | _ :: rest -> lemma_all_true i rho rest

let rec lemma_some_true (i:interpretation value) (rho:env value) (args:list expr)
  : Lemma (ensures some_true (eval_args i args rho) <==> clause_holds i rho args) (decreases args)
  = match args with
    | [] -> ()
    | _ :: rest -> lemma_some_true i rho rest

let rec lemma_bit_values (i:interpretation value) (rho:env value) (args:list expr)
  : Lemma (ensures L.map BR.bool_value (eval_args i args rho) == BV.bit_values i rho args)
          (decreases args)
  = match args with
    | [] -> ()
    | _ :: rest -> lemma_bit_values i rho rest

let rec lemma_bits_number (bs:list bool)
  : Lemma (ensures BV.bits_number bs < pow2 (L.length bs)) (decreases bs)
  = match bs with
    | [] -> ()
    | _ :: rest -> lemma_bits_number rest

let lemma_ground_app (f:func_decl) (args:list expr)
  : Lemma (requires closed_ground (App f args))
          (ensures ground_args args /\ D.scoped_args [] args /\ sorts_match args f.domain)
  = ()

let rec lemma_ground_args_mem (args:list expr) (a:expr)
  : Lemma (requires ground_args args /\ L.memP a args) (ensures ground a) (decreases args)
  = match args with
    | b :: rest -> if b = a then () else lemma_ground_args_mem rest a

(* --- Bounds on concatenated values ------------------------------------- *)

let lemma_concat_bound (m n:pos) (a b:int)
  : Lemma (requires 0 <= a /\ a < pow2 m /\ 0 <= b /\ b < pow2 n)
          (ensures 0 <= a * pow2 n + b /\ a * pow2 n + b < pow2 (m + n))
  = M.pow2_plus m n;
    M.lemma_mult_le_right (pow2 n) a (pow2 m - 1);
    M.nat_times_nat_is_nat a (pow2 n)

let lemma_zero_extend_bound (w:pos) (k:nat) (a:int)
  : Lemma (requires 0 <= a /\ a < pow2 w) (ensures a < pow2 (w + k))
  = M.pow2_le_compat (w + k) w

let lemma_extract_bound (k:pos) (a:int) : Lemma (0 <= a % pow2 k /\ a % pow2 k < pow2 k) = ()

(* --- The Boolean contracts --------------------------------------------- *)

let lemma_boolean_typing (leaf:func_decl -> list value -> int) (a:expr) (rho:env value)
  : Lemma (closed_ground a /\ get_sort a == bool_sort ==> VBool? (eval (standard leaf) a rho))
  = if ground a then lemma_ground_fits leaf a rho

let lemma_constants (leaf:func_decl -> list value -> int) (f:func_decl) (rho:env value)
  : Lemma ((C.canonical_true f ==> eval (standard leaf) (App f []) rho == VBool true) /\
           (C.canonical_false f ==> eval (standard leaf) (App f []) rho == VBool false))
  = ()

let lemma_negation (leaf:func_decl -> list value -> int) (f:func_decl) (a:expr) (rho:env value)
  : Lemma (C.canonical_not f /\ closed_ground (App f [a]) ==>
           ((eval (standard leaf) (App f [a]) rho == VBool true) ==
            (eval (standard leaf) a rho == VBool false)))
  = ()

let lemma_conjunction (leaf:func_decl -> list value -> int) (f:func_decl) (args:list expr) (rho:env value)
  : Lemma (C.canonical_and f /\ closed_ground (App f args) ==>
           (eval (standard leaf) (App f args) rho == VBool true <==> conj_holds (standard leaf) rho args))
  = lemma_all_true (standard leaf) rho args

let lemma_disjunction (leaf:func_decl -> list value -> int) (f:func_decl) (args:list expr) (rho:env value)
  : Lemma (C.canonical_or f /\ closed_ground (App f args) ==>
           (eval (standard leaf) (App f args) rho == VBool true <==> clause_holds (standard leaf) rho args))
  = lemma_some_true (standard leaf) rho args

let lemma_implication (leaf:func_decl -> list value -> int) (f:func_decl) (a b:expr) (rho:env value)
  : Lemma (C.canonical_implies f /\ closed_ground (App f [a; b]) ==>
           (eval (standard leaf) (App f [a; b]) rho == VBool true <==>
            (lit_true (standard leaf) rho a ==> lit_true (standard leaf) rho b)))
  = ()

let lemma_equality (leaf:func_decl -> list value -> int) (f:func_decl) (a b:expr) (rho:env value)
  : Lemma (C.canonical_eq f /\ closed_ground (App f [a; b]) ==>
           (eval (standard leaf) (App f [a; b]) rho == VBool true <==>
            eval (standard leaf) a rho == eval (standard leaf) b rho))
  = if C.canonical_eq f && closed_ground (App f [a; b]) then (
      let i = standard leaf in
      lemma_ground_fits leaf a rho;
      lemma_ground_fits leaf b rho;
      lemma_fits_scalar (get_sort a) (eval i a rho);
      lemma_fits_scalar (get_sort b) (eval i b rho);
      lemma_value_eq (eval i a rho) (eval i b rho))

let lemma_ground_boolean (leaf:func_decl -> list value -> int)
  : Lemma (ground_boolean (standard leaf))
  = FStar.Classical.forall_intro_2 (lemma_boolean_typing leaf);
    FStar.Classical.forall_intro_2 (lemma_constants leaf);
    FStar.Classical.forall_intro_3 (lemma_negation leaf);
    FStar.Classical.forall_intro_3 (lemma_conjunction leaf);
    FStar.Classical.forall_intro_3 (lemma_disjunction leaf);
    FStar.Classical.forall_intro_4 (lemma_implication leaf);
    FStar.Classical.forall_intro_4 (lemma_equality leaf)

(* --- The bit-vector contracts ------------------------------------------ *)

let lemma_injective (leaf:func_decl -> list value -> int) (width:pos) (a b:expr) (rho:env value)
  : Lemma (width <= max_width /\ closed_ground a /\ closed_ground b /\
           get_sort a == BV.bv_sort width /\ get_sort b == BV.bv_sort width ==>
           ((eval (standard leaf) a rho == eval (standard leaf) b rho <==>
             std_project width (eval (standard leaf) a rho) == std_project width (eval (standard leaf) b rho)) /\
            0 <= std_project width (eval (standard leaf) a rho) /\
            std_project width (eval (standard leaf) a rho) < pow2 width))
  = if width <= max_width && closed_ground a && closed_ground b &&
       get_sort a = BV.bv_sort width && get_sort b = BV.bv_sort width then (
      lemma_ground_fits leaf a rho;
      lemma_ground_fits leaf b rho;
      lemma_fits_bv width (eval (standard leaf) a rho);
      lemma_fits_bv width (eval (standard leaf) b rho))

let lemma_numeral (leaf:func_decl -> list value -> int) (e:expr) (rho:env value) (width:pos) (n:int)
  : Lemma (BV.numeral e == Some (width, n) ==> std_project width (eval (standard leaf) e rho) == n)
  = match BV.numeral e with
    | Some (w, k) ->
      if w = width && k = n then (
        match e with
        | App f [] ->
          lemma_width width;
          lemma_bool_width ();
          lemma_bvv width n)
    | None -> ()

let lemma_operation (leaf:func_decl -> list value -> int) (f:func_decl) (args:list expr) (rho:env value)
                    (width:pos) (op:decl_kind)
  : Lemma (closed_ground (App f args) /\ BV.operation f args == Some (width, op) ==>
           std_project width (eval (standard leaf) (App f args) rho) ==
           BV.calculate width op (BV.words width std_project (eval_args (standard leaf) args rho)))
  = if BV.operation f args = Some (width, op) then (
      let vs = eval_args (standard leaf) args rho in
      lemma_eval_args_length (standard leaf) args rho;
      lemma_width width;
      lemma_bool_width ();
      lemma_bvv width (BV.calculate width op (BV.words width std_project vs)))

let lemma_nary_operation (leaf:func_decl -> list value -> int) (f:func_decl) (args:list expr) (rho:env value)
                         (width:pos) (op:decl_kind)
  : Lemma (closed_ground (App f args) /\ BV.nary_operation f args == Some (width, op) ==>
           std_project width (eval (standard leaf) (App f args) rho) ==
           BV.calculate_nary width op (BV.words width std_project (eval_args (standard leaf) args rho)))
  = if BV.nary_operation f args = Some (width, op) then (
      let vs = eval_args (standard leaf) args rho in
      lemma_eval_args_length (standard leaf) args rho;
      lemma_width width;
      lemma_bool_width ();
      lemma_bvv width (BV.calculate_nary width op (BV.words width std_project vs)))

let lemma_extract (leaf:func_decl -> list value -> int) (e:expr) (rho:env value) (s:BV.extraction)
  : Lemma (closed_ground e /\ BV.extract_parts e == Some s ==>
           std_project (s.BV.high - s.BV.low + 1) (eval (standard leaf) e rho) ==
             (std_project s.BV.source_width (eval (standard leaf) s.BV.operand rho) / pow2 s.BV.low) %
             pow2 (s.BV.high - s.BV.low + 1))
  = if BV.extract_parts e = Some s then (
      match e with
      | App f [x] ->
        (match f.int_params with
         | [w; h; l] ->
           let i = standard leaf in
           let vx = eval i x rho in
           let k : pos = h - l + 1 in
           let r = (std_project w vx / pow2 l) % pow2 k in
           assert (s.BV.operand == x /\ s.BV.source_width == w /\ s.BV.high == h /\ s.BV.low == l /\
                   f.interp == Some BV.op_extract /\ f.range == BV.bv_sort k /\ k <= max_width);
           assert (eval_args i [x] rho == [vx]);
           assert (bool_raw f [vx] == None);
           assert (bv_raw f [vx] == Some (bvv k r));
           lemma_extract_bound k (std_project w vx / pow2 l);
           lemma_width k;
           lemma_bool_width ();
           lemma_bvv k r))

let lemma_concat (leaf:func_decl -> list value -> int) (e:expr) (rho:env value) (c:BV.concatenation)
  : Lemma (closed_ground e /\ BV.concat_parts e == Some c ==>
           std_project (c.BV.left_width + c.BV.right_width) (eval (standard leaf) e rho) ==
             std_project c.BV.left_width (eval (standard leaf) c.BV.left rho) * pow2 c.BV.right_width +
             std_project c.BV.right_width (eval (standard leaf) c.BV.right rho))
  = if BV.concat_parts e = Some c then (
      match e with
      | App f [x; y] ->
        (match f.int_params with
         | [m; n] ->
           let i = standard leaf in
           let vx = eval i x rho in
           let vy = eval i y rho in
           let a = std_project m vx in
           let b = std_project n vy in
           assert (c.BV.left == x /\ c.BV.right == y /\ c.BV.left_width == m /\
                   c.BV.right_width == n /\ f.interp == Some BV.op_concat);
           assert (eval_args i [x; y] rho == [vx; vy]);
           assert (bool_raw f [vx; vy] == None);
           assert (bv_raw f [vx; vy] == Some (bvv (m + n) (a * pow2 n + b)));
           lemma_concat_bound m n a b;
           lemma_width (m + n);
           lemma_bool_width ();
           lemma_bvv (m + n) (a * pow2 n + b)))

let lemma_zero_extend (leaf:func_decl -> list value -> int) (e:expr) (rho:env value) (s:BV.zero_extension)
  : Lemma (closed_ground e /\ BV.zero_extend_parts e == Some s ==>
           std_project (s.BV.input_width + s.BV.extra_width) (eval (standard leaf) e rho) ==
             std_project s.BV.input_width (eval (standard leaf) s.BV.argument rho))
  = if BV.zero_extend_parts e = Some s then (
      match e with
      | App f [x] ->
        (match f.int_params with
         | [w; k] ->
           let i = standard leaf in
           let vx = eval i x rho in
           let a = std_project w vx in
           assert (s.BV.argument == x /\ s.BV.input_width == w /\ s.BV.extra_width == k /\
                   f.interp == Some BV.op_zero_extend /\ f.range == BV.bv_sort (w + k) /\
                   w + k <= max_width);
           assert (eval_args i [x] rho == [vx]);
           assert (bool_raw f [vx] == None);
           assert (bv_raw f [vx] == Some (bvv (w + k) a));
           lemma_zero_extend_bound w k a;
           lemma_width (w + k);
           lemma_bool_width ();
           lemma_bvv (w + k) a))

let lemma_word (leaf:func_decl -> list value -> int) (e:expr) (rho:env value) (width:pos) (args:list expr)
  : Lemma (closed_ground e /\ BV.word_parts e == Some (width, args) ==>
           std_project width (eval (standard leaf) e rho) ==
           BV.bits_number (BV.bit_values (standard leaf) rho args))
  = if BV.word_parts e = Some (width, args) then (
      let i = standard leaf in
      lemma_bit_values i rho args;
      lemma_eval_args_length i args rho;
      lemma_bits_number (L.map BR.bool_value (eval_args i args rho));
      FStar.List.Tot.Properties.map_lemma BR.bool_value (eval_args i args rho);
      lemma_width width;
      lemma_bool_width ();
      lemma_bvv width (BV.bits_number (BV.bit_values i rho args)))

let lemma_unsigned (leaf:func_decl -> list value -> int) (e:expr) (rho:env value) (c:BV.unsigned_comparison)
  : Lemma (closed_ground e /\ BV.unsigned_parts e == Some c ==>
           eval (standard leaf) e rho ==
           VBool (BV.unsigned_value c.BV.relation
             (std_project c.BV.width (eval (standard leaf) c.BV.lhs rho))
             (std_project c.BV.width (eval (standard leaf) c.BV.rhs rho))))
  = if BV.unsigned_parts e = Some c then (
      match e with
      | App f [x; y] ->
        (match f.int_params with
         | [w] ->
           let i = standard leaf in
           let vx = eval i x rho in
           let vy = eval i y rho in
           let r = VBool (BV.unsigned_value c.BV.relation (std_project w vx) (std_project w vy)) in
           assert (c.BV.lhs == x /\ c.BV.rhs == y /\ c.BV.width == w /\ f.interp == Some c.BV.relation /\
                   unsigned_kind c.BV.relation /\ f.range == bool_sort);
           assert (eval_args i [x; y] rho == [vx; vy]);
           assert (bool_raw f [vx; vy] == None);
           assert (bv_raw f [vx; vy] == Some r);
           assert (fits bool_sort r)))

let lemma_concat3 (leaf:func_decl -> list value -> int) (e:expr) (rho:env value) (c:BV.concatenation3)
  : Lemma (concat3_at (standard leaf) std_project e rho c)
  = if BV.concat3_parts e = Some c then (
      match e with
      | App f [x; y; z] ->
        (match f.int_params with
         | [p; q; t] ->
           let i = standard leaf in
           let vx = eval i x rho in
           let vy = eval i y rho in
           let vz = eval i z rho in
           let a = std_project p vx in
           let b = std_project q vy in
           let d = std_project t vz in
           let r = a * pow2 (q + t) + b * pow2 t + d in
           assert (c.BV.first == x /\ c.BV.second == y /\ c.BV.third == z /\ c.BV.width1 == p /\
                   c.BV.width2 == q /\ c.BV.width3 == t /\ f.interp == Some BV.op_concat /\
                   f.range == BV.bv_sort (p + q + t) /\ p + q + t <= max_width);
           assert (eval_args i [x; y; z] rho == [vx; vy; vz]);
           assert (bool_raw f [vx; vy; vz] == None);
           assert (bv_raw f [vx; vy; vz] == Some (bvv (p + q + t) r));
           lemma_concat_bound q t b d;
           lemma_concat_bound p (q + t) a (b * pow2 t + d);
           lemma_width (p + q + t);
           lemma_bool_width ();
           lemma_bvv (p + q + t) r))

let lemma_bv_values (leaf:func_decl -> list value -> int)
  : Lemma (bv_values (standard leaf) std_project)
  = FStar.Classical.forall_intro_4 (lemma_injective leaf)

let lemma_bv_numerals (leaf:func_decl -> list value -> int)
  : Lemma (bv_numerals (standard leaf) std_project)
  = FStar.Classical.forall_intro_4 (lemma_numeral leaf)

let lemma_bv_operations (leaf:func_decl -> list value -> int)
  : Lemma (bv_operations (standard leaf) std_project)
  = introduce forall (f:func_decl) (args:list expr) (rho:env value) (width:pos) (op:decl_kind).
      (closed_ground (App f args) /\ BV.operation f args == Some (width, op) ==>
       std_project width (eval (standard leaf) (App f args) rho) ==
       BV.calculate width op (BV.words width std_project (eval_args (standard leaf) args rho)))
    with lemma_operation leaf f args rho width op

let lemma_bv_nary_operations (leaf:func_decl -> list value -> int)
  : Lemma (bv_nary_operations (standard leaf) std_project)
  = introduce forall (f:func_decl) (args:list expr) (rho:env value) (width:pos) (op:decl_kind).
      (closed_ground (App f args) /\ BV.nary_operation f args == Some (width, op) ==>
       std_project width (eval (standard leaf) (App f args) rho) ==
       BV.calculate_nary width op (BV.words width std_project (eval_args (standard leaf) args rho)))
    with lemma_nary_operation leaf f args rho width op

let lemma_bv_extracts (leaf:func_decl -> list value -> int)
  : Lemma (bv_extracts (standard leaf) std_project)
  = FStar.Classical.forall_intro_3 (lemma_extract leaf)

let lemma_bv_concats (leaf:func_decl -> list value -> int)
  : Lemma (bv_concats (standard leaf) std_project)
  = FStar.Classical.forall_intro_3 (lemma_concat leaf)

let lemma_bv_zero_extends (leaf:func_decl -> list value -> int)
  : Lemma (bv_zero_extends (standard leaf) std_project)
  = FStar.Classical.forall_intro_3 (lemma_zero_extend leaf)

let lemma_bv_words (leaf:func_decl -> list value -> int)
  : Lemma (bv_words (standard leaf) std_project)
  = FStar.Classical.forall_intro_4 (lemma_word leaf)

let lemma_bv_unsigned (leaf:func_decl -> list value -> int)
  : Lemma (bv_unsigned (standard leaf) std_project)
  = FStar.Classical.forall_intro_3 (lemma_unsigned leaf)

let lemma_bv_concats3 (leaf:func_decl -> list value -> int)
  : Lemma (bv_concats3 (standard leaf) std_project)
  = FStar.Classical.forall_intro_3 (lemma_concat3 leaf)

let lemma_ground_bv (leaf:func_decl -> list value -> int)
  : Lemma (ground_bv (standard leaf) std_project)
  = lemma_bv_values leaf;
    lemma_bv_numerals leaf;
    lemma_bv_operations leaf;
    lemma_bv_nary_operations leaf;
    lemma_bv_extracts leaf;
    lemma_bv_concats leaf;
    lemma_bv_zero_extends leaf;
    lemma_bv_words leaf;
    lemma_bv_unsigned leaf;
    lemma_bv_concats3 leaf

(* --- The ground contracts have models ---------------------------------- *)

let lemma_standard_model (leaf:func_decl -> list value -> int)
  : Lemma (ground_model (standard leaf) std_project)
  = lemma_ground_boolean leaf;
    lemma_ground_bv leaf

let lemma_ground_model_inhabited ()
  : Lemma (exists (i:interpretation value) (project:pos -> value -> int). ground_model i project)
  = lemma_standard_model (fun _ _ -> 0)

(* The opaque leaves are not fixed by the model: an uninterpreted constant
   of sort `BV<w>` takes every value in [0, 2^w) in some standard model. *)
let lemma_opaque_constant (c:func_decl) (w:pos) (r:int) (rho:env value)
  : Lemma (requires c.interp == None /\ c.range == BV.bv_sort w /\ w <= max_width /\ 0 <= r /\ r < pow2 w)
          (ensures std_project w (eval (standard (fun _ _ -> r)) (App c []) rho) == r)
  = lemma_width w;
    lemma_bool_width ();
    lemma_bvv w r

(* --- The global contracts imply the ground ones ------------------------- *)

(* Each ground contract is a global one with a narrower antecedent: a
   canonical connective carries the name the global contract is keyed by,
   and a closed ground term is scoped. So every theorem proved from
   `ground_model` also holds under the global hypotheses, which is how
   the kernel, still stated over `Z3UnifiedProof.model_sound`, reaches it.
   Those global hypotheses have no model (see the header), so this
   implication is formally vacuous and is NOT the evidence for the ground
   fragment. The evidence is `lemma_standard_model` together with the
   theorems proved from `ground_model` itself
   (`Z3BvExhaustive.lemma_valid_ground`, `lemma_valid_standard`). *)
let lemma_ground_boolean_of_global (i:interpretation value)
  : Lemma (requires Z3ObservationalEquality.boolean_model i /\ not_sound i /\ and_sound i /\
                    or_sound i /\ implies_sound i /\ eq_sound i /\ true_sound i /\ false_sound i)
          (ensures ground_boolean i)
  = ()

let lemma_ground_bv_of_global (i:interpretation value) (project:pos -> value -> int)
  : Lemma (requires BV.bv_model i project) (ensures ground_bv i project)
  = ()

let lemma_ground_of_global (i:interpretation value) (project:pos -> value -> int)
  : Lemma (requires BV.bv_model i project /\ Z3ObservationalEquality.boolean_model i /\
                    not_sound i /\ and_sound i /\ or_sound i /\ implies_sound i /\ eq_sound i /\
                    true_sound i /\ false_sound i)
          (ensures ground_model i project)
  = lemma_ground_boolean_of_global i;
    lemma_ground_bv_of_global i project

(* --- Reading the ground contracts ---------------------------------------- *)

let closed_args (args:list expr) : bool = ground_args args && D.scoped_args [] args

let lemma_closed_app (f:func_decl) (args:list expr)
  : Lemma (requires closed_ground (App f args)) (ensures closed_args args /\ sorts_match args f.domain)
  = ()

let lemma_closed_cons (a:expr) (rest:list expr)
  : Lemma (requires closed_args (a :: rest)) (ensures closed_ground a /\ closed_args rest)
  = ()

let lemma_ground_word (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                      (width:pos) (e:expr)
  : Lemma (requires ground_bv i project /\ closed_ground e /\ get_sort e == BV.bv_sort width /\
                    width <= max_width)
          (ensures 0 <= project width (eval i e rho) /\ project width (eval i e rho) < pow2 width /\
                   U.to_uint_t width (project width (eval i e rho)) == project width (eval i e rho))
  = assert (0 <= project width (eval i e rho) /\ project width (eval i e rho) < pow2 width);
    M.small_mod (project width (eval i e rho)) (pow2 width)

let lemma_ground_equal (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                       (width:pos) (a b:expr)
  : Lemma (requires ground_bv i project /\ closed_ground a /\ closed_ground b /\
                    get_sort a == BV.bv_sort width /\ get_sort b == BV.bv_sort width /\ width <= max_width)
          (ensures (eval i a rho == eval i b rho) <==> project width (eval i a rho) == project width (eval i b rho))
  = ()

let lemma_ground_operation (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                           (f:func_decl) (args:list expr) (width:pos) (op:decl_kind)
  : Lemma (requires ground_bv i project /\ closed_ground (App f args) /\
                    BV.operation f args == Some (width, op))
          (ensures width <= max_width /\
                   project width (eval i (App f args) rho) ==
                   BV.calculate width op (BV.words width project (eval_args i args rho)))
  = ()

let lemma_ground_extract (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                         (e:expr) (s:BV.extraction)
  : Lemma (requires ground_bv i project /\ closed_ground e /\ BV.extract_parts e == Some s)
          (ensures closed_ground s.BV.operand /\ get_sort s.BV.operand == BV.bv_sort s.BV.source_width /\
                   s.BV.source_width <= max_width /\
                   get_sort e == BV.bv_sort (s.BV.high - s.BV.low + 1) /\
                   project (s.BV.high - s.BV.low + 1) (eval i e rho) ==
                     (project s.BV.source_width (eval i s.BV.operand rho) / pow2 s.BV.low) %
                     pow2 (s.BV.high - s.BV.low + 1))
  = match e with App _ [_] -> () | _ -> ()

let lemma_ground_concat (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                        (e:expr) (c:BV.concatenation)
  : Lemma (requires ground_bv i project /\ closed_ground e /\ BV.concat_parts e == Some c)
          (ensures closed_ground c.BV.left /\ closed_ground c.BV.right /\
                   get_sort c.BV.left == BV.bv_sort c.BV.left_width /\
                   get_sort c.BV.right == BV.bv_sort c.BV.right_width /\
                   c.BV.left_width + c.BV.right_width <= max_width /\
                   get_sort e == BV.bv_sort (c.BV.left_width + c.BV.right_width) /\
                   project (c.BV.left_width + c.BV.right_width) (eval i e rho) ==
                     project c.BV.left_width (eval i c.BV.left rho) * pow2 c.BV.right_width +
                     project c.BV.right_width (eval i c.BV.right rho))
  = match e with App _ [_; _] -> () | _ -> ()

let lemma_ground_zero_extend (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                             (e:expr) (s:BV.zero_extension)
  : Lemma (requires ground_bv i project /\ closed_ground e /\ BV.zero_extend_parts e == Some s)
          (ensures closed_ground s.BV.argument /\ get_sort s.BV.argument == BV.bv_sort s.BV.input_width /\
                   s.BV.input_width + s.BV.extra_width <= max_width /\
                   get_sort e == BV.bv_sort (s.BV.input_width + s.BV.extra_width) /\
                   project (s.BV.input_width + s.BV.extra_width) (eval i e rho) ==
                     project s.BV.input_width (eval i s.BV.argument rho))
  = match e with App _ [_] -> () | _ -> ()

let lemma_ground_unsigned (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                          (e:expr) (c:BV.unsigned_comparison)
  : Lemma (requires ground_bv i project /\ closed_ground e /\ BV.unsigned_parts e == Some c)
          (ensures c.BV.width <= max_width /\ closed_ground c.BV.lhs /\ closed_ground c.BV.rhs /\
                   get_sort c.BV.lhs == BV.bv_sort c.BV.width /\ get_sort c.BV.rhs == BV.bv_sort c.BV.width /\
                   eval i e rho == VBool (BV.unsigned_value c.BV.relation
                     (project c.BV.width (eval i c.BV.lhs rho)) (project c.BV.width (eval i c.BV.rhs rho))))
  = match e with App _ [_; _] -> () | _ -> ()
