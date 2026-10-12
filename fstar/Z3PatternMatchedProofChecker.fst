(*
   Z3PatternMatchedProofChecker.fst

   `Z3InterpretedProofChecker.fst` discharges `all_leaves_sound` for
   four hand-picked, literal `Rewrite` leaves (one per theory), each
   built from fixed named constants (`a`, `i`, `v`, ...): proving each
   leaf sound is a one-line call into the matching theory lemma
   because the shapes of the sub-expressions involved are "obviously"
   right by construction.

   This file *generalizes* one of those four patterns --
   `select(store(a,i,x),i) = x`, `Z3ArrayTheory.lemma_select_store_same`
   -- into a genuine, purely structural (no Meta-F*/tactics needed)
   *pattern-matching compiler*: a decidable recognizer
   (`match_select_store_same`) that looks at the *shape* of a
   `Rewrite s t` leaf and, whenever it fits the select-store-same
   schema for *arbitrary* array/index/value sub-expressions `a`/`idx`/
   `x` (not just the four literal named constants from
   `Z3InterpretedProofChecker.fst`), automatically proves
   `all_leaves_sound` for that leaf by invoking
   `Z3ArrayTheory.lemma_select_store_same` on whatever values those
   sub-expressions denote.

   Why this needs more than string/AST matching: `interp_app`'s
   pattern match (e.g. for `op_select`,
   `match args with | [VArr a; VInt i] -> ... | _ -> VInt 0`) silently
   falls back to a dummy value for ill-shaped arguments. So recognizing
   `select(store(a,i,x),i)` for arbitrary `a`/`i`/`x` is only sound if
   those sub-expressions are *guaranteed* -- by their declared sorts --
   to actually evaluate to `VArr`/`VInt`/`VInt`. `lemma_eval_shape`
   below is exactly that guarantee: a structural "type soundness"
   lemma, proved once by induction over `expr`, that every
   well-formed (`wf`), `decls_ok`, closed, quantifier-free expression
   evaluates (under `Z3InterpretedProofChecker.the_interpretation`) to
   a `value` whose constructor matches its declared sort. `expr`,
   `func_decl`, and `sort` have no function-typed fields (`interp` is
   an `option decl_kind` tag, not a semantic function), so this
   induction -- and the whole matcher -- is plain, decidable F*
   structural recursion; no tactics are required.

   Known limitation (documented, not solved here): the companion
   pattern `select(store(a,i,x),j) = select(a,j)` for `i <> j`
   (`Z3ArrayTheory.lemma_select_store_diff`) is *not* generalized by
   this file. `Z3InterpretedProofChecker`'s `uninterp_app`/
   `default_value` maps *every* uninterpreted 0-ary constant of a
   given sort to the *same* value regardless of name, so two
   syntactically distinct named Int constants `i`/`j` currently always
   denote the *same* `VInt`, making the semantic side condition `i <>
   j` unsatisfiable for any two currently-expressible named constants
   under this interpretation. Supporting it generically would need
   `uninterp_app` to inject distinct constant names to distinct
   values (e.g. by hashing `decl_name`), which is left as future work.
*)
module Z3PatternMatchedProofChecker

open Z3AstTheory
open Z3ProofTheory
open Z3InterpretedProofChecker

(* ----------------------------------------------------------------- *)
(* 1. A decidable "declared shape is self-consistent with its          *)
(*    `the_interpretation` semantics" predicate.                       *)
(*                                                                     *)
(*    `wf` (`Z3AstTheory.fst`) only checks that an `App`'s args match   *)
(*    its *own* declared domain; it says nothing about whether a       *)
(*    given `f.interp = Some k` tag is consistent with the specific    *)
(*    domain/range `interp_app` actually expects for that `k`. That    *)
(*    binding is `Z3InterpretedProofChecker.fst`'s choice, not         *)
(*    anything `Z3AstTheory.fst` enforces, so it is closed here.       *)
(* ----------------------------------------------------------------- *)

let decl_shape_ok (f:func_decl) : bool =
  match f.interp with
  | None -> true
  | Some k ->
    if k = op_not then f.domain = [bool_s] && sort_eq f.range bool_s
    else if k = op_plus then f.domain = [int_s; int_s] && sort_eq f.range int_s
    else if k = op_select then f.domain = [arr_s; int_s] && sort_eq f.range int_s
    else if k = op_store then f.domain = [arr_s; int_s; int_s] && sort_eq f.range arr_s
    else if k = op_bvand then f.domain = [bv_s; bv_s] && sort_eq f.range bv_s
    else if k = op_concat then f.domain = [seq_s; seq_s] && sort_eq f.range seq_s
    else false (* some other interpreted op: not trusted by this file *)

let rec decls_ok (e:expr) : Tot bool (decreases e) =
  match e with
  | Var _ _ -> true
  | App f args -> decl_shape_ok f && decls_ok_args args
  | Quantifier _ _ body -> decls_ok body

and decls_ok_args (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: args' -> decls_ok a && decls_ok_args args'

(* No `Quantifier` node anywhere: sidesteps needing the general,
   binding-depth-indexed version of `lemma_eval_shape` (every leaf
   this file matches is built purely from constants/applications). *)
let rec no_quant (e:expr) : Tot bool (decreases e) =
  match e with
  | Var _ _ -> true
  | App _ args -> no_quant_args args
  | Quantifier _ _ _ -> false

and no_quant_args (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: args' -> no_quant a && no_quant_args args'

(* ----------------------------------------------------------------- *)
(* 2. The value-shape predicate, keyed by declared sort name, mirroring*)
(*    `Z3InterpretedProofChecker.default_value`'s own case split.      *)
(*    "Lambda" (a quantifier's sort) is left unconstrained: nothing in *)
(*    this file ever needs a shape obligation for it.                  *)
(* ----------------------------------------------------------------- *)

let shape_ok (v:value) (srt:sort) : bool =
  match srt.sort_name with
  | "Bool" -> VBool? v
  | "BV32" -> VBV? v
  | "SeqInt" -> VSeq? v
  | "ArrayIntInt" -> VArr? v
  | "Lambda" -> true
  | _ (* "Int" and anything else *) -> VInt? v

let rec shapes_ok (vs:list value) (srts:list sort) : Tot bool (decreases vs) =
  match vs, srts with
  | [], [] -> true
  | v :: vs', s :: srts' -> shape_ok v s && shapes_ok vs' srts'
  | _, _ -> false

let rec get_sorts (args:list expr) : Tot (list sort) (decreases args) =
  match args with
  | [] -> []
  | a :: args' -> get_sort a :: get_sorts args'

let lemma_shape_ok_sort_eq (v:value) (s1 s2:sort)
  : Lemma (requires sort_eq s1 s2 /\ shape_ok v s1) (ensures shape_ok v s2)
  = ()

let rec lemma_shapes_ok_sorts_match (args:list expr) (dom:list sort) (vs:list value)
  : Lemma (requires sorts_match args dom /\ shapes_ok vs (get_sorts args))
          (ensures shapes_ok vs dom)
          (decreases args)
  = match args, dom, vs with
    | [], [], [] -> ()
    | a :: args', d :: dom', v :: vs' ->
      lemma_shape_ok_sort_eq v (get_sort a) d;
      lemma_shapes_ok_sorts_match args' dom' vs'
    | _, _, _ -> ()

let lemma_default_value_shape_ok (srt:sort)
  : Lemma (shape_ok (default_value srt) srt)
  = match srt.sort_name with
    | "Bool" -> ()
    | "BV32" -> ()
    | "SeqInt" -> ()
    | "ArrayIntInt" -> ()
    | _ -> ()

(* ----------------------------------------------------------------- *)
(* 3. The central structural "type soundness" lemma: a well-formed,     *)
(*    quantifier-free, closed, `decls_ok` expression's value always    *)
(*    has the shape its declared sort promises.                        *)
(* ----------------------------------------------------------------- *)

let rec lemma_eval_shape (e:expr) (rho:env value)
  : Lemma (requires wf e /\ decls_ok e /\ closed e /\ no_quant e)
          (ensures shape_ok (eval the_interpretation e rho) (get_sort e))
          (decreases e)
  = match e with
    | Var _ _ -> ()        (* impossible: `closed e` forbids any `Var` here *)
    | Quantifier _ _ _ -> () (* impossible: ruled out by `no_quant e` *)
    | App f args ->
      lemma_eval_shape_args args rho;
      let vs = eval_args the_interpretation args rho in
      (match f.interp with
       | None -> lemma_default_value_shape_ok f.range
       | Some k ->
         lemma_shapes_ok_sorts_match args f.domain vs;
         if k = op_not then
           (match vs with
            | [VBool b] -> ()
            | _ -> ())
         else if k = op_plus then
           (match vs with
            | [VInt a; VInt b] -> ()
            | _ -> ())
         else if k = op_select then
           (match vs with
            | [VArr a; VInt i] -> ()
            | _ -> ())
         else if k = op_store then
           (match vs with
            | [VArr a; VInt i; VInt x] -> ()
            | _ -> ())
         else if k = op_bvand then
           (match vs with
            | [VBV a; VBV b] -> ()
            | _ -> ())
         else if k = op_concat then
           (match vs with
            | [VSeq a; VSeq b] -> ()
            | _ -> ())
         else ()) (* `decl_shape_ok f` is `false` here: contradiction *)

and lemma_eval_shape_args (args:list expr) (rho:env value)
  : Lemma (requires wf_args args /\ decls_ok_args args /\ closed_at_args 0 args /\ no_quant_args args)
          (ensures shapes_ok (eval_args the_interpretation args rho) (get_sorts args))
          (decreases args)
  = match args with
    | [] -> ()
    | a :: args' ->
      lemma_eval_shape a rho;
      lemma_eval_shape_args args' rho

(* ----------------------------------------------------------------- *)
(* 4. The matcher: recognize `select(store(a,idx,x),idx) = x` for      *)
(*    arbitrary `a`/`idx`/`x`, purely structurally (decidable `expr`    *)
(*    equality -- no higher-order/function fields anywhere in `expr`). *)
(* ----------------------------------------------------------------- *)

let match_select_store_same (s t:expr) : option (expr & expr & expr) =
  match s with
  | App f_sel [App f_sto [a; idx1; x]; idx2] ->
    if Some? f_sel.interp && Some?.v f_sel.interp = op_select &&
       Some? f_sto.interp && Some?.v f_sto.interp = op_store &&
       idx1 = idx2 && t = x
    then Some (a, idx1, x)
    else None
  | _ -> None

let select_store_same_leaf_ok (s t:expr) : bool =
  match match_select_store_same s t with
  | None -> false
  | Some (a, idx, x) ->
    wf s && wf t && closed s && closed t && decls_ok s && decls_ok t && no_quant s && no_quant t &&
    sort_eq (get_sort a) arr_s && sort_eq (get_sort idx) int_s && sort_eq (get_sort x) int_s

let lemma_select_store_same_leaf_sound (s t:expr)
  : Lemma (requires select_store_same_leaf_ok s t)
          (ensures all_leaves_sound the_interpretation (mk_rewrite_leaf s t))
  = match s with
    | App f_sel [App f_sto [a; idx1; x]; idx2] ->
      let aux (rho:env value)
        : Lemma (eval the_interpretation s rho == eval the_interpretation t rho)
        = lemma_eval_shape a rho;
          lemma_eval_shape idx1 rho;
          lemma_eval_shape x rho;
          (match eval the_interpretation a rho, eval the_interpretation idx1 rho, eval the_interpretation x rho with
           | VArr av, VInt iv, VInt xv ->
             Z3ArrayTheory.lemma_select_store_same av iv xv
           | _, _, _ -> ())
      in
      FStar.Classical.forall_intro aux
    | _ -> ()

(* ----------------------------------------------------------------- *)
(* 5. Whole-proof-tree closure: a decidable checker mirroring           *)
(*    `all_leaves_sound`'s own recursion, matching every `Rewrite` leaf *)
(*    against the select-store-same schema, plus its soundness proof.  *)
(* ----------------------------------------------------------------- *)

let rec all_matched (p:proof) : Tot bool (decreases p) =
  match p with
  | Refl _ -> true
  | Sym p1 -> all_matched p1
  | Trans p1 p2 -> all_matched p1 && all_matched p2
  | Congr _ _ _ prfs -> all_matched_list prfs
  | Rewrite s t -> select_store_same_leaf_ok s t
  | QuantIntro _ _ p1 -> all_matched p1

and all_matched_list (prfs:list proof) : Tot bool (decreases prfs) =
  match prfs with
  | [] -> true
  | p :: prfs' -> all_matched p && all_matched_list prfs'

let rec lemma_all_matched_sound (p:proof)
  : Lemma (requires all_matched p)
          (ensures all_leaves_sound the_interpretation p)
          (decreases p)
  = match p with
    | Refl _ -> ()
    | Sym p1 -> lemma_all_matched_sound p1
    | Trans p1 p2 -> lemma_all_matched_sound p1; lemma_all_matched_sound p2
    | Congr _ _ _ prfs -> lemma_all_matched_list_sound prfs
    | Rewrite s t -> lemma_select_store_same_leaf_sound s t
    | QuantIntro _ _ p1 -> lemma_all_matched_sound p1

and lemma_all_matched_list_sound (prfs:list proof)
  : Lemma (requires all_matched_list prfs)
          (ensures all_leaves_sound_list the_interpretation prfs)
          (decreases prfs)
  = match prfs with
    | [] -> ()
    | p :: prfs' -> lemma_all_matched_sound p; lemma_all_matched_list_sound prfs'

(* ----------------------------------------------------------------- *)
(* 6. End-to-end: any proof tree the structural checker accepts        *)
(*    (`Some? (fact p)`) whose `Rewrite` leaves all fit the            *)
(*    select-store-same schema (`all_matched p`) denotes a *true*      *)
(*    equation under `the_interpretation` -- with no hand-wired,       *)
(*    per-example trust, however deeply the array/index/value          *)
(*    sub-expressions are nested.                                      *)
(* ----------------------------------------------------------------- *)

let lemma_matched_proof_true (p:proof) (rho:env value)
  : Lemma (requires Some? (fact p) /\ all_matched p)
          (ensures (let Some (a1, a2) = fact p in
                    eval the_interpretation a1 rho == eval the_interpretation a2 rho))
  = lemma_all_matched_sound p;
    lemma_quant_extensional ();
    lemma_proof_sound the_interpretation p rho

(* ----------------------------------------------------------------- *)
(* 7. Demonstration: a *new*, non-trivial, nested example -- distinct  *)
(*    from `Z3InterpretedProofChecker.array_leaf`'s literal named       *)
(*    constants `a`/`i`/`v` -- proving the generalization is genuine.   *)
(*    `select(store(f(x), i+i, g(y)), i+i) = g(y)`, where `f`/`g` are   *)
(*    uninterpreted functions and `i+i` is a compound index expression.*)
(* ----------------------------------------------------------------- *)

let f_d : func_decl = { decl_name = "f_arr"; domain = [int_s]; range = arr_s; interp = None; int_params = [] }
let g_d : func_decl = { decl_name = "g_val"; domain = [int_s]; range = int_s; interp = None; int_params = [] }
let x_c = c0 (konst "x" int_s)
let y_c = c0 (konst "y" int_s)
let i_c = c0 (konst "i" int_s)

let fx : expr = c1 f_d x_c
let gy : expr = c1 g_d y_c
let ii : expr = c2 (interpreted "+" [int_s; int_s] int_s op_plus) i_c i_c

let nested_store = c3 store_d fx ii gy
let nested_leaf : proof = mk_rewrite_leaf (c2 select_d nested_store ii) gy

let lemma_nested_leaf_matched ()
  : Lemma (all_matched nested_leaf)
  = ()

let lemma_nested_leaf_true (rho:env value)
  : Lemma (eval the_interpretation (c2 select_d nested_store ii) rho ==
           eval the_interpretation gy rho)
  = lemma_nested_leaf_matched ();
    lemma_matched_proof_true nested_leaf rho
