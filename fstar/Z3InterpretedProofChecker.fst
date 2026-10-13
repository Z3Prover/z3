(*
   Z3InterpretedProofChecker.fst

   Wires `Z3ArrayTheory.fst`, `Z3SeqTheory.fst`/`Z3SeqRewrites.fst`,
   `Z3BvTheory.fst`/`Z3BvRewriter.fst`, and `Z3BoolRewriter.fst`'s
   already-proven lemmas directly into the `Z3ProofTheory.fst`/
   `Z3PulseProofChecker.fst` proof calculus, by constructing one
   concrete `interpretation value` under which several of
   `Z3PulseProofCheckerTests.fst`'s `Rewrite` leaves are not merely
   *trusted* (as discussed: `all_leaves_sound` is normally an
   unverified caller-side hypothesis, exactly mirroring Z3's own
   `proof_checker.cpp::check1_basic`'s `PR_REWRITE` handling) but
   *actually proved sound*, by literally invoking the matching
   per-theory lemma.

   This does not change how the checker itself works (it is still,
   correctly, theory-agnostic and still trusts `Rewrite` leaves as
   leaves -- see `Z3PulseProofChecker.fst`); it discharges, for a
   handful of concrete example leaves, the `all_leaves_sound`
   obligation that every real deployment of the checker leaves to its
   caller.
*)
module Z3InterpretedProofChecker
open FStar.FunctionalExtensionality
open Z3AstTheory
open Z3ProofTheory
open Z3ValueTheory

(* `value` and every `op_*` decl_kind constant used below now live in
   `Z3ValueTheory.fst` (see that file's docstring for why): this is
   what lets `Z3ArrayInterp.fst`/`Z3SeqInterp.fst`/`Z3BvInterp.fst`
   each expose their own theory-scoped `interp_app` without a circular
   module dependency on this file. `bv32_value` similarly moved to
   `Z3BvInterp.fst`, next to the one `op_num_bv` case that needs it. *)

(* ----------------------------------------------------------------- *)
(* An injective `string -> nat` encoding, used only so that two        *)
(* *distinctly-named* 0-ary uninterpreted Int constants (e.g. `i`/`j`  *)
(* in `select (store a i x) j == select a j`) are provably given        *)
(* *different* denotations by `uninterp_app` below -- strong enough to *)
(* discharge a `requires i <> j` side condition such as                *)
(* `Z3ArrayTheory.lemma_select_store_diff`'s, which was previously      *)
(* unsatisfiable for any two named constants (see the "Known           *)
(* limitation" note this replaces in `Z3PatternMatchedProofChecker.fst`).*)
(* `char_base` exceeds every Unicode scalar value `int_of_char` can      *)
(* return, so `encode_chars` is a clean base-`char_base` positional      *)
(* encoding (verified by straightforward induction, no extra hints).    *)
(* ----------------------------------------------------------------- *)

let char_base : pos = 0x110001

let rec encode_chars (cs:list FStar.Char.char) : Tot nat (decreases cs) =
  match cs with
  | [] -> 0
  | c :: cs' -> FStar.Char.int_of_char c + char_base * (1 + encode_chars cs')

let rec lemma_encode_chars_injective (cs1 cs2:list FStar.Char.char)
  : Lemma (requires encode_chars cs1 == encode_chars cs2)
          (ensures cs1 == cs2)
          (decreases cs1)
  = match cs1, cs2 with
    | [], [] -> ()
    | c1 :: cs1', c2 :: cs2' -> lemma_encode_chars_injective cs1' cs2'
    | _, _ -> ()

let string_key (s:string) : nat = encode_chars (FStar.String.list_of_string s)

let lemma_string_key_injective (s1 s2:string)
  : Lemma (requires string_key s1 == string_key s2) (ensures s1 == s2)
  = lemma_encode_chars_injective (FStar.String.list_of_string s1) (FStar.String.list_of_string s2);
    FStar.String.string_of_list_of_string s1;
    FStar.String.string_of_list_of_string s2

(* Contrapositive form, the one the `select_store_diff` matcher needs. *)
let lemma_string_key_distinct (s1 s2:string)
  : Lemma (requires s1 <> s2) (ensures string_key s1 <> string_key s2)
  = if string_key s1 = string_key s2 then lemma_string_key_injective s1 s2

(* A total, symmetric boolean equality over `value`, used by the        *)
(* `eq_symm` rewrite matcher. `VArr` wraps a function type with no       *)
(* decidable equality, so two array-valued arguments are (soundly)       *)
(* reported unequal; this under-approximation is never exercised by      *)
(* `op_eq`'s actual uses below, which only ever compare `VInt`/`VBool`/   *)
(* `VBV`/`VSeq` arguments extracted from closed Z3 equality leaves.       *)
let value_eq_sym (a b:value) : bool =
  match a, b with
  | VInt x, VInt y -> x = y
  | VBool x, VBool y -> x = y
  | VBV x, VBV y -> x = y
  | VSeq x, VSeq y -> x = y
  | _, _ -> false

let lemma_value_eq_sym_symmetric (a b:value)
  : Lemma (value_eq_sym a b == value_eq_sym b a)
  = ()

(* A fixed, sort-respecting default value, used as the (otherwise
   arbitrary) denotation of every uninterpreted 0-ary constant. Since
   every leaf's claimed equation below is itself a closed instance of
   an already-*universally*-quantified theory lemma (`forall a i x. ...`),
   any well-sorted choice of witness works; picking one fixed default
   per sort is the simplest one that type-checks. *)
let default_value (s:sort) : value =
  if sort_eq s (BaseSort "Bool") then VBool false
  else if sort_eq s (BaseSort "BV32") then VBV 0
  else if sort_eq s (BaseSort "SeqInt") then VSeq []
  else if sort_eq s (ArraySort [BaseSort "Int"] (BaseSort "Int")) then VArr (on int (fun _ -> 0))
  else (* "Int" and anything else *) VInt 0

(* Each "core" decl_kind (bool/arith/`eq`/literal ops with no dedicated
   theory file of their own) still gets its own small, independently-
   checked top-level function here, same rationale as before. Array/
   seq/bv ops now live in their own theory-scoped `interp_app`
   (`Z3ArrayInterp.fst`/`Z3SeqInterp.fst`/`Z3BvInterp.fst`). *)
let interp_not (args:list value) : value =
  match args with
  | [VBool b] -> VBool (not b)
  | _ -> VInt 0

let interp_plus (args:list value) : value =
  match args with
  | [VInt a; VInt b] -> VInt (a + b)
  | _ -> VInt 0

let interp_eq (args:list value) : value =
  match args with
  | [a; b] -> VBool (value_eq_sym a b)
  | _ -> VInt 0

let interp_true () : value = VBool true

let interp_false () : value = VBool false

let interp_num_int (int_params:list int) : value =
  match int_params with
  | [v] -> VInt v
  | _ -> VInt 0

(* Binary `and`/`or`/`=>`; see `Z3ValueTheory.op_and`/`op_or`/
   `op_implies`'s docstring. *)
let interp_and (args:list value) : value =
  match args with
  | [VBool a; VBool b] -> VBool (a && b)
  | _ -> VInt 0

let interp_or (args:list value) : value =
  match args with
  | [VBool a; VBool b] -> VBool (a || b)
  | _ -> VInt 0

let interp_implies (args:list value) : value =
  match args with
  | [VBool a; VBool b] -> VBool ((not a) || b)
  | _ -> VInt 0

(* "Core" dispatch (bool/arith/`eq`/literals); tried only after every
   theory's own `interp_app` has already had a chance to claim `k`. *)
let core_interp_app (k:decl_kind) (int_params:list int) (args:list value) : value =
  if k = op_not then interp_not args
  else if k = op_plus then interp_plus args
  else if k = op_eq then interp_eq args
  else if k = op_true then interp_true ()
  else if k = op_false then interp_false ()
  else if k = op_num_int then interp_num_int int_params
  else if k = op_and then interp_and args
  else if k = op_or then interp_or args
  else if k = op_implies then interp_implies args
  (* Unreachable for every well-sorted term built below; `eval`'s type
     does not statically rule it out (see `Z3AstTheory.fst`'s own
     comment on `interp_app`/`uninterp_app` being total on `list
     value` of unconstrained length), so a total fallback is required. *)
  else VInt 0

(* The top-level dispatcher: each theory is tried in turn via its own
   `interp_app`, which returns `Some v` only for the `decl_kind`s it
   owns; the first theory to claim `k` wins, and `core_interp_app`
   (bool/arith/`eq`/literals) is the final fallback before the total
   default. This mirrors the same "small, independently-checked
   pieces, trivial composition" shape as the per-op decomposition
   above/below it (and the reason this refactor was requested: so each
   theory's interpretation is owned, extended, and re-verified
   independently of every other theory's). *)
let interp_app (f:func_decl{Some? f.interp}) (args:list value) : value =
  let k = Some?.v f.interp in
  match Z3ArrayInterp.interp_app k f.int_params args with
  | Some v -> v
  | None ->
  match Z3SeqInterp.interp_app k f.int_params args with
  | Some v -> v
  | None ->
  match Z3BvInterp.interp_app k f.int_params args with
  | Some v -> v
  | None -> core_interp_app k f.int_params args

(* 0-ary, Int-sorted uninterpreted constants are now injected via
   `string_key` into *distinct* `VInt`s whenever they have *distinct*
   `decl_name`s -- strong enough to discharge a `requires i <> j` side
   condition (see `lemma_string_key_distinct` above). Every other
   uninterpreted application (non-0-ary, or non-Int-sorted) keeps the
   old fixed-default-per-sort denotation; nothing in this file's
   existing proofs relies on *which* value a named constant gets
   (only on well-sortedness), so this refinement is a conservative
   extension. *)
let uninterp_app (f:func_decl{is_uninterp_decl f}) (args:list value) : value =
  match args with
  | [] -> if sort_eq f.range (BaseSort "Int") then VInt (string_key f.decl_name) else default_value f.range
  | _ -> default_value f.range

(* `interp_quant` is never exercised by any fact proved in this file
   (none of the example leaves below sit under a quantifier), so any
   well-typed, *extensional* choice suffices; a constant function is
   the simplest one, and makes `quant_extensional` hold trivially. *)
let interp_quant (_:quantifier_kind) (_:list sort) (_:list value -> value) : value = VBool true

let the_interpretation : interpretation value = {
  interp_app; uninterp_app; interp_quant;
}

let lemma_quant_extensional ()
  : Lemma (quant_extensional the_interpretation)
  = ()

(* ----------------------------------------------------------------- *)
(* One-step `eval` unfolding helpers. `eval`/`eval_args` are `let rec`  *)
(* over `expr`/`list expr`; for a *concrete* head constructor (`App f   *)
(* args` with `args` a literal, fixed-length list) this is a single    *)
(* non-recursive step once `args` itself is fully evaluated, which     *)
(* F*'s normalizer/SMT encoding discharges automatically for `()`      *)
(* proofs below -- stated explicitly here only for documentation.      *)
(* ----------------------------------------------------------------- *)

let s (n:string) : sort = BaseSort n
let int_s = s "Int"
let bool_s = s "Bool"
let bv_s = s "BV32"
let seq_s = s "SeqInt"
let arr_s = ArraySort [int_s] int_s

let konst (name:string) (rng:sort) : func_decl =
  { decl_name = name; domain = []; range = rng; interp = None; int_params = [] }
let interpreted (name:string) (dom:list sort) (rng:sort) (k:decl_kind) : func_decl =
  { decl_name = name; domain = dom; range = rng; interp = Some k; int_params = [] }

let c0 (f:func_decl) : expr = App f []
let c1 (f:func_decl) (a:expr) : expr = App f [a]
let c2 (f:func_decl) (a b:expr) : expr = App f [a; b]
let c3 (f:func_decl) (a b c:expr) : expr = App f [a; b; c]

(* ----------------------------------------------------------------- *)
(* Array: `select(store(a,i,v),i) = v` --                              *)
(* `Z3ArrayTheory.lemma_select_store_same`, the same fact `array_leaf` *)
(* in `Z3PulseProofCheckerTests.fst` uses (and the `array:select` tag   *)
(* the now-reverted C++ tagging mechanism extracted from a real        *)
(* `(get-proof)` run -- see `REWRITE_RULE_TAGS_REPORT.md`).             *)
(* ----------------------------------------------------------------- *)

let a_arr = c0 (konst "a" arr_s)
let i_i = c0 (konst "i" int_s)
let v_i = c0 (konst "v" int_s)
let select_d = interpreted "select" [arr_s; int_s] int_s op_select
let store_d = interpreted "store" [arr_s; int_s; int_s] arr_s op_store
let store_aiv = c3 store_d a_arr i_i v_i
let array_leaf : proof = mk_rewrite_leaf (c2 select_d store_aiv i_i) v_i

let lemma_array_leaf_sound ()
  : Lemma (all_leaves_sound the_interpretation array_leaf)
  = let g : Z3ArrayTheory.arr int int = on int (fun _ -> 0) in
    Z3ArrayTheory.lemma_select_store_same g 0 0

let lemma_array_leaf_true (rho:env value)
  : Lemma (eval the_interpretation (c2 select_d store_aiv i_i) rho ==
           eval the_interpretation v_i rho)
  = lemma_array_leaf_sound ();
    lemma_quant_extensional ();
    lemma_proof_sound the_interpretation array_leaf rho

(* ----------------------------------------------------------------- *)
(* Seq: concatenation associativity -- `Z3SeqRewrites.lemma_concat_assoc`,*)
(* the exact leaf `mixed_chain`'s first step uses in                    *)
(* `Z3PulseProofCheckerTests.fst`.                                      *)
(* ----------------------------------------------------------------- *)

let a_sq = c0 (konst "a" seq_s)
let b_sq = c0 (konst "b" seq_s)
let c_sq = c0 (konst "c" seq_s)
let cat_d = interpreted "++" [seq_s; seq_s] seq_s op_concat
let seq_leaf : proof =
  mk_rewrite_leaf (c2 cat_d (c2 cat_d a_sq b_sq) c_sq) (c2 cat_d a_sq (c2 cat_d b_sq c_sq))

let lemma_seq_leaf_sound ()
  : Lemma (all_leaves_sound the_interpretation seq_leaf)
  = let e : Z3SeqTheory.seq int = [] in
    Z3SeqRewrites.lemma_concat_assoc e e e

(* ----------------------------------------------------------------- *)
(* Bool: double-negation elimination -- `Z3BoolRewriter.not_not`.      *)
(* ----------------------------------------------------------------- *)

let x_b = c0 (konst "x" bool_s)
let not_d = interpreted "not" [bool_s] bool_s op_not
let bool_leaf : proof = mk_rewrite_leaf (c1 not_d (c1 not_d x_b)) x_b

let lemma_bool_leaf_sound ()
  : Lemma (all_leaves_sound the_interpretation bool_leaf)
  = Z3BoolRewriter.not_not false

(* ----------------------------------------------------------------- *)
(* BV: `bvand` idempotence -- `Z3BvRewriter.lemma_bvand_self`.          *)
(* ----------------------------------------------------------------- *)

let y_bv = c0 (konst "y" bv_s)
let bvand_d = interpreted "bvand" [bv_s; bv_s] bv_s op_bvand
let bv_leaf : proof = mk_rewrite_leaf (c2 bvand_d y_bv y_bv) y_bv

let lemma_bv_leaf_sound ()
  : Lemma (all_leaves_sound the_interpretation bv_leaf)
  = Z3BvRewriter.lemma_bvand_self #32 0

(* ----------------------------------------------------------------- *)
(* End-to-end: for each of the four leaves above, the Pulse/pure       *)
(* checker's accepted conclusion is not just well-formed but actually  *)
(* *true*, under `the_interpretation`, because the specific per-theory *)
(* lemma was invoked above -- not merely assumed via `all_leaves_sound`.*)
(* ----------------------------------------------------------------- *)

let lemma_seq_leaf_true (rho:env value)
  : Lemma (eval the_interpretation (c2 cat_d (c2 cat_d a_sq b_sq) c_sq) rho ==
           eval the_interpretation (c2 cat_d a_sq (c2 cat_d b_sq c_sq)) rho)
  = lemma_seq_leaf_sound ();
    lemma_quant_extensional ();
    lemma_proof_sound the_interpretation seq_leaf rho

let lemma_bool_leaf_true (rho:env value)
  : Lemma (eval the_interpretation (c1 not_d (c1 not_d x_b)) rho ==
           eval the_interpretation x_b rho)
  = lemma_bool_leaf_sound ();
    lemma_quant_extensional ();
    lemma_proof_sound the_interpretation bool_leaf rho

let lemma_bv_leaf_true (rho:env value)
  : Lemma (eval the_interpretation (c2 bvand_d y_bv y_bv) rho ==
           eval the_interpretation y_bv rho)
  = lemma_bv_leaf_sound ();
    lemma_quant_extensional ();
    lemma_proof_sound the_interpretation bv_leaf rho
