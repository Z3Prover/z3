(*
   Z3PatternMatchedProofChecker.fst

   `Z3InterpretedProofChecker.fst` discharges `all_leaves_sound` for
   four hand-picked, literal `Rewrite` leaves (one per theory), each
   built from fixed named constants (`a`, `i`, `v`, ...): proving each
   leaf sound is a one-line call into the matching theory lemma
   because the shapes of the sub-expressions involved are "obviously"
   right by construction.

   This file *generalizes* those literal examples into a genuine,
   purely structural (no Meta-F*/tactics needed) *pattern-matching
   compiler*: a library of decidable recognizers, one per
   already-proven rewrite-rule lemma, each looking at the *shape* of a
   `Rewrite s t` leaf and, whenever it fits that lemma's schema for
   *arbitrary* sub-expressions (not just literal named constants),
   automatically proving `all_leaves_sound` for that leaf by invoking
   the matching theory lemma on whatever values those sub-expressions
   denote. Six patterns are covered this way (§4):
   `select(store(a,i,x),i) = x`, `store(store(a,i,x),i,y) =
   store(a,i,y)`, `store(a,i,select(a,i)) = a`
   (`Z3ArrayTheory.lemma_select_store_same`/`lemma_store_same_twice`/
   `lemma_store_redundant`), `(a++b)++c = a++(b++c)`
   (`Z3SeqRewrites.lemma_concat_assoc`), `not(not(x)) = x`
   (`Z3BoolRewriter.not_not`), and `bvand(y,y) = y`
   (`Z3BvRewriter.lemma_bvand_self`).

   Not every `Rewrite` leaf fits one of these six schemas -- Z3's
   rewriters encode many more rewrite rules than this (or any single
   bounded) pattern library can realistically enumerate. Rather than
   either trusting the whole proof tree unconditionally
   (`all_leaves_sound`, the pre-existing baseline) or rejecting
   anything not recognized (`all_matched`, all-or-nothing, §6), §7
   adds a *partial* mode: `collect_unmatched` walks a proof tree and
   returns the exact list of `Rewrite` leaves none of the six matchers
   recognize, and `lemma_partial_proof_true` proves the whole
   derivation's conclusion true *given only* that the collected
   leftover leaves are semantically sound -- i.e. every already-matched
   leaf, however many or however deeply nested, needs no further
   trust, and the caller's remaining proof obligation is reduced to
   exactly, and only, the leaves this library does not (yet) cover.

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
open FStar.List.Tot

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
(* 4. The matcher *library*: six structural recognizers, one per       *)
(*    already-proven rewrite-rule lemma that (a) needs no semantic     *)
(*    side condition beyond shapes (contrast `lemma_select_store_diff`,*)
(*    `lemma_store_commute`: both require `i <> j`, which is            *)
(*    unsatisfiable for any two distinct named constants under          *)
(*    `the_interpretation` -- see the module docstring's "known         *)
(*    limitation"), and (b) is expressible purely with the six          *)
(*    interpreted ops `Z3InterpretedProofChecker.fst` already gives     *)
(*    real semantics to (`select`/`store`/`not`/`plus`/`bvand`/`concat`,*)
(*    i.e. no new `const`/`ite`/`map` operator semantics is added       *)
(*    here). Every leftover array/seq/bool/bv lemma this file does      *)
(*    *not* match (`lemma_select_const`, `lemma_select_ite`,            *)
(*    `lemma_select_lambda`, `lemma_lambda_eta`, `lemma_select_map1/2`, *)
(*    `lemma_map2_store/const/lambda`, `lemma_array_extensionality`,    *)
(*    the `set_*` lemmas, `lemma_eq_const_*`, and anything from         *)
(*    `Z3SeqAxioms`/`Z3SeqDerive`/`Z3ArithRewriter`/etc. not already     *)
(*    wired into `the_interpretation`) is not silently ignored: §5-6    *)
(*    below turn every `Rewrite` leaf that fails all six matchers into  *)
(*    an explicit, collected *leftover proof obligation* instead.       *)
(* ----------------------------------------------------------------- *)

(* 4a. `select(store(a,idx,x),idx) = x` -- `Z3ArrayTheory.lemma_select_store_same`. *)

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

(* 4b. `store(store(a,idx,x),idx,y) = store(a,idx,y)` --
       `Z3ArrayTheory.lemma_store_same_twice`. *)

let match_store_same_twice (s t:expr) : option (expr & expr & expr & expr) =
  match s, t with
  | App f1 [App f2 [a; i1; x]; i2; y], App f3 [a'; i3; y'] ->
    if Some? f1.interp && Some?.v f1.interp = op_store &&
       Some? f2.interp && Some?.v f2.interp = op_store &&
       Some? f3.interp && Some?.v f3.interp = op_store &&
       i1 = i2 && i2 = i3 && a = a' && y = y'
    then Some (a, i1, x, y)
    else None
  | _, _ -> None

let store_same_twice_leaf_ok (s t:expr) : bool =
  match match_store_same_twice s t with
  | None -> false
  | Some (a, i, x, y) ->
    wf s && wf t && closed s && closed t && decls_ok s && decls_ok t && no_quant s && no_quant t &&
    sort_eq (get_sort a) arr_s && sort_eq (get_sort i) int_s &&
    sort_eq (get_sort x) int_s && sort_eq (get_sort y) int_s

let lemma_store_same_twice_leaf_sound (s t:expr)
  : Lemma (requires store_same_twice_leaf_ok s t)
          (ensures all_leaves_sound the_interpretation (mk_rewrite_leaf s t))
  = match s, t with
    | App f1 [App f2 [a; i1; x]; i2; y], App f3 [a'; i3; y'] ->
      let aux (rho:env value)
        : Lemma (eval the_interpretation s rho == eval the_interpretation t rho)
        = lemma_eval_shape a rho;
          lemma_eval_shape i1 rho;
          lemma_eval_shape x rho;
          lemma_eval_shape y rho;
          (match eval the_interpretation a rho, eval the_interpretation i1 rho,
                 eval the_interpretation x rho, eval the_interpretation y rho with
           | VArr av, VInt iv, VInt xv, VInt yv ->
             Z3ArrayTheory.lemma_store_same_twice av iv xv yv
           | _, _, _, _ -> ())
      in
      FStar.Classical.forall_intro aux
    | _, _ -> ()

(* 4c. `store(a,idx,select(a,idx)) = a` -- `Z3ArrayTheory.lemma_store_redundant`. *)

let match_store_redundant (s t:expr) : option (expr & expr) =
  match s with
  | App f_sto [a; i; App f_sel [a2; i2]] ->
    if Some? f_sto.interp && Some?.v f_sto.interp = op_store &&
       Some? f_sel.interp && Some?.v f_sel.interp = op_select &&
       a = a2 && i = i2 && t = a
    then Some (a, i)
    else None
  | _ -> None

let store_redundant_leaf_ok (s t:expr) : bool =
  match match_store_redundant s t with
  | None -> false
  | Some (a, i) ->
    wf s && wf t && closed s && closed t && decls_ok s && decls_ok t && no_quant s && no_quant t &&
    sort_eq (get_sort a) arr_s && sort_eq (get_sort i) int_s

let lemma_store_redundant_leaf_sound (s t:expr)
  : Lemma (requires store_redundant_leaf_ok s t)
          (ensures all_leaves_sound the_interpretation (mk_rewrite_leaf s t))
  = match s with
    | App f_sto [a; i; App f_sel [a2; i2]] ->
      let aux (rho:env value)
        : Lemma (eval the_interpretation s rho == eval the_interpretation t rho)
        = lemma_eval_shape a rho;
          lemma_eval_shape i rho;
          (match eval the_interpretation a rho, eval the_interpretation i rho with
           | VArr av, VInt iv -> Z3ArrayTheory.lemma_store_redundant av iv
           | _, _ -> ())
      in
      FStar.Classical.forall_intro aux
    | _ -> ()

(* 4d. `(a++b)++c = a++(b++c)` -- `Z3SeqRewrites.lemma_concat_assoc`. *)

let match_concat_assoc (s t:expr) : option (expr & expr & expr) =
  match s, t with
  | App f1 [App f2 [a; b]; c], App f3 [a'; App f4 [b'; c']] ->
    if Some? f1.interp && Some?.v f1.interp = op_concat &&
       Some? f2.interp && Some?.v f2.interp = op_concat &&
       Some? f3.interp && Some?.v f3.interp = op_concat &&
       Some? f4.interp && Some?.v f4.interp = op_concat &&
       a = a' && b = b' && c = c'
    then Some (a, b, c)
    else None
  | _, _ -> None

let concat_assoc_leaf_ok (s t:expr) : bool =
  match match_concat_assoc s t with
  | None -> false
  | Some (a, b, c) ->
    wf s && wf t && closed s && closed t && decls_ok s && decls_ok t && no_quant s && no_quant t &&
    sort_eq (get_sort a) seq_s && sort_eq (get_sort b) seq_s && sort_eq (get_sort c) seq_s

let lemma_concat_assoc_leaf_sound (s t:expr)
  : Lemma (requires concat_assoc_leaf_ok s t)
          (ensures all_leaves_sound the_interpretation (mk_rewrite_leaf s t))
  = match s, t with
    | App f1 [App f2 [a; b]; c], App f3 [a'; App f4 [b'; c']] ->
      let aux (rho:env value)
        : Lemma (eval the_interpretation s rho == eval the_interpretation t rho)
        = lemma_eval_shape a rho;
          lemma_eval_shape b rho;
          lemma_eval_shape c rho;
          (match eval the_interpretation a rho, eval the_interpretation b rho, eval the_interpretation c rho with
           | VSeq av, VSeq bv, VSeq cv -> Z3SeqRewrites.lemma_concat_assoc av bv cv
           | _, _, _ -> ())
      in
      FStar.Classical.forall_intro aux
    | _, _ -> ()

(* 4e. `not(not(x)) = x` -- `Z3BoolRewriter.not_not`. *)

let match_not_not (s t:expr) : option expr =
  match s with
  | App f1 [App f2 [x]] ->
    if Some? f1.interp && Some?.v f1.interp = op_not &&
       Some? f2.interp && Some?.v f2.interp = op_not && t = x
    then Some x
    else None
  | _ -> None

let not_not_leaf_ok (s t:expr) : bool =
  match match_not_not s t with
  | None -> false
  | Some x ->
    wf s && wf t && closed s && closed t && decls_ok s && decls_ok t && no_quant s && no_quant t &&
    sort_eq (get_sort x) bool_s

let lemma_not_not_leaf_sound (s t:expr)
  : Lemma (requires not_not_leaf_ok s t)
          (ensures all_leaves_sound the_interpretation (mk_rewrite_leaf s t))
  = match s with
    | App f1 [App f2 [x]] ->
      let aux (rho:env value)
        : Lemma (eval the_interpretation s rho == eval the_interpretation t rho)
        = lemma_eval_shape x rho;
          (match eval the_interpretation x rho with
           | VBool xv -> Z3BoolRewriter.not_not xv
           | _ -> ())
      in
      FStar.Classical.forall_intro aux
    | _ -> ()

(* 4f. `bvand(y,y) = y` -- `Z3BvRewriter.lemma_bvand_self`. *)

let match_bvand_self (s t:expr) : option expr =
  match s with
  | App f [y1; y2] ->
    if Some? f.interp && Some?.v f.interp = op_bvand && y1 = y2 && t = y1
    then Some y1
    else None
  | _ -> None

let bvand_self_leaf_ok (s t:expr) : bool =
  match match_bvand_self s t with
  | None -> false
  | Some y ->
    wf s && wf t && closed s && closed t && decls_ok s && decls_ok t && no_quant s && no_quant t &&
    sort_eq (get_sort y) bv_s

let lemma_bvand_self_leaf_sound (s t:expr)
  : Lemma (requires bvand_self_leaf_ok s t)
          (ensures all_leaves_sound the_interpretation (mk_rewrite_leaf s t))
  = match s with
    | App f [y1; y2] ->
      let aux (rho:env value)
        : Lemma (eval the_interpretation s rho == eval the_interpretation t rho)
        = lemma_eval_shape y1 rho;
          (match eval the_interpretation y1 rho with
           | VBV yv -> Z3BvRewriter.lemma_bvand_self #32 yv
           | _ -> ())
      in
      FStar.Classical.forall_intro aux
    | _ -> ()

(* ----------------------------------------------------------------- *)
(* 5. The combinator: try every matcher above in turn, and the          *)
(*    corresponding "matched implies sound" lemma (a case split over    *)
(*    the six, invoking whichever matcher actually fired).              *)
(* ----------------------------------------------------------------- *)

let try_match_leaf (s t:expr) : bool =
  select_store_same_leaf_ok s t ||
  store_same_twice_leaf_ok s t ||
  store_redundant_leaf_ok s t ||
  concat_assoc_leaf_ok s t ||
  not_not_leaf_ok s t ||
  bvand_self_leaf_ok s t

let lemma_try_match_leaf_sound (s t:expr)
  : Lemma (requires try_match_leaf s t)
          (ensures all_leaves_sound the_interpretation (mk_rewrite_leaf s t))
  = if select_store_same_leaf_ok s t then lemma_select_store_same_leaf_sound s t
    else if store_same_twice_leaf_ok s t then lemma_store_same_twice_leaf_sound s t
    else if store_redundant_leaf_ok s t then lemma_store_redundant_leaf_sound s t
    else if concat_assoc_leaf_ok s t then lemma_concat_assoc_leaf_sound s t
    else if not_not_leaf_ok s t then lemma_not_not_leaf_sound s t
    else lemma_bvand_self_leaf_sound s t

(* ----------------------------------------------------------------- *)
(* 6. "Fully matched" mode: a decidable whole-proof-tree checker         *)
(*    mirroring `all_leaves_sound`'s own recursion, requiring *every*    *)
(*    `Rewrite` leaf to fit one of the six schemas above.                *)
(* ----------------------------------------------------------------- *)

let rec all_matched (p:proof) : Tot bool (decreases p) =
  match p with
  | Refl _ -> true
  | Sym p1 -> all_matched p1
  | Trans p1 p2 -> all_matched p1 && all_matched p2
  | Congr _ _ _ prfs -> all_matched_list prfs
  | Rewrite s t -> try_match_leaf s t
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
    | Rewrite s t -> lemma_try_match_leaf_sound s t
    | QuantIntro _ _ p1 -> lemma_all_matched_sound p1

and lemma_all_matched_list_sound (prfs:list proof)
  : Lemma (requires all_matched_list prfs)
          (ensures all_leaves_sound_list the_interpretation prfs)
          (decreases prfs)
  = match prfs with
    | [] -> ()
    | p :: prfs' -> lemma_all_matched_sound p; lemma_all_matched_list_sound prfs'

let lemma_matched_proof_true (p:proof) (rho:env value)
  : Lemma (requires Some? (fact p) /\ all_matched p)
          (ensures (let Some (a1, a2) = fact p in
                    eval the_interpretation a1 rho == eval the_interpretation a2 rho))
  = lemma_all_matched_sound p;
    lemma_quant_extensional ();
    lemma_proof_sound the_interpretation p rho

(* ----------------------------------------------------------------- *)
(* 7. "Partial" mode: rather than requiring `all_matched p` (all-or-    *)
(*    nothing), *collect* every `Rewrite` leaf that no matcher          *)
(*    recognizes into an explicit list of leftover `(s, t)` proof       *)
(*    obligations, and prove that semantic soundness of just that       *)
(*    leftover list suffices for the whole proof's conclusion -- i.e.   *)
(*    the caller only has to separately verify (by whatever means,      *)
(*    e.g. a future matcher, or a direct per-leaf argument) exactly the *)
(*    leaves this file's matcher library does not yet cover, instead    *)
(*    of either the whole tree (`all_leaves_sound`, the unconditional   *)
(*    trust baseline) or nothing (`all_matched`, all-or-nothing).       *)
(* ----------------------------------------------------------------- *)

let rec collect_unmatched (p:proof) : Tot (list (expr & expr)) (decreases p) =
  match p with
  | Refl _ -> []
  | Sym p1 -> collect_unmatched p1
  | Trans p1 p2 -> collect_unmatched p1 @ collect_unmatched p2
  | Congr _ _ _ prfs -> collect_unmatched_list prfs
  | Rewrite s t -> if try_match_leaf s t then [] else [(s, t)]
  | QuantIntro _ _ p1 -> collect_unmatched p1

and collect_unmatched_list (prfs:list proof) : Tot (list (expr & expr)) (decreases prfs) =
  match prfs with
  | [] -> []
  | p :: prfs' -> collect_unmatched p @ collect_unmatched_list prfs'

(* "Every `(s, t)` pair in this obligation list is semantically sound." *)
let leftover_sound (obligations:list (expr & expr)) : prop =
  forall (st:(expr & expr)). List.Tot.mem st obligations ==>
    (forall (rho:env value). eval the_interpretation (fst st) rho == eval the_interpretation (snd st) rho)

let rec lemma_mem_app_left (#a:eqtype) (x:a) (l1 l2:list a)
  : Lemma (requires List.Tot.mem x l1) (ensures List.Tot.mem x (l1 @ l2)) (decreases l1)
  = match l1 with
    | h :: t -> if h = x then () else lemma_mem_app_left x t l2

let rec lemma_mem_app_right (#a:eqtype) (x:a) (l1 l2:list a)
  : Lemma (requires List.Tot.mem x l2) (ensures List.Tot.mem x (l1 @ l2)) (decreases l1)
  = match l1 with
    | [] -> ()
    | h :: t -> lemma_mem_app_right x t l2

let lemma_leftover_sound_append_split (l1 l2:list (expr & expr))
  : Lemma (requires leftover_sound (l1 @ l2))
          (ensures leftover_sound l1 /\ leftover_sound l2)
  = let aux1 (st:(expr & expr))
      : Lemma (requires List.Tot.mem st l1)
              (ensures (forall (rho:env value). eval the_interpretation (fst st) rho == eval the_interpretation (snd st) rho))
      = lemma_mem_app_left st l1 l2
    in
    let aux2 (st:(expr & expr))
      : Lemma (requires List.Tot.mem st l2)
              (ensures (forall (rho:env value). eval the_interpretation (fst st) rho == eval the_interpretation (snd st) rho))
      = lemma_mem_app_right st l1 l2
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux1);
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux2)

let rec lemma_collect_unmatched_sound (p:proof)
  : Lemma (requires leftover_sound (collect_unmatched p))
          (ensures all_leaves_sound the_interpretation p)
          (decreases p)
  = match p with
    | Refl _ -> ()
    | Sym p1 -> lemma_collect_unmatched_sound p1
    | Trans p1 p2 ->
      lemma_leftover_sound_append_split (collect_unmatched p1) (collect_unmatched p2);
      lemma_collect_unmatched_sound p1;
      lemma_collect_unmatched_sound p2
    | Congr _ _ _ prfs -> lemma_collect_unmatched_list_sound prfs
    | Rewrite s t ->
      if try_match_leaf s t then lemma_try_match_leaf_sound s t
      else begin
        assert (collect_unmatched p == [(s, t)]);
        assert (List.Tot.mem (s, t) (collect_unmatched p))
      end  (* `leftover_sound (collect_unmatched p)` instantiated at `(s,t)` now
              gives exactly `all_leaves_sound`'s `Rewrite` case. *)
    | QuantIntro _ _ p1 -> lemma_collect_unmatched_sound p1

and lemma_collect_unmatched_list_sound (prfs:list proof)
  : Lemma (requires leftover_sound (collect_unmatched_list prfs))
          (ensures all_leaves_sound_list the_interpretation prfs)
          (decreases prfs)
  = match prfs with
    | [] -> ()
    | p :: prfs' ->
      lemma_leftover_sound_append_split (collect_unmatched p) (collect_unmatched_list prfs');
      lemma_collect_unmatched_sound p;
      lemma_collect_unmatched_list_sound prfs'

(* End-to-end "partial" theorem: a proof tree the structural checker
   accepts is true *given* semantic soundness of exactly its leftover,
   unmatched leaves -- the minimal extra trust this file's matcher
   library cannot discharge on its own. *)
let lemma_partial_proof_true (p:proof) (rho:env value)
  : Lemma (requires Some? (fact p) /\ leftover_sound (collect_unmatched p))
          (ensures (let Some (a1, a2) = fact p in
                    eval the_interpretation a1 rho == eval the_interpretation a2 rho))
  = lemma_collect_unmatched_sound p;
    lemma_quant_extensional ();
    lemma_proof_sound the_interpretation p rho

(* ----------------------------------------------------------------- *)
(* 8. Demonstration 1: a *new*, non-trivial, nested example -- distinct*)
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

(* ----------------------------------------------------------------- *)
(* 9. Demonstration 2: a *mixed* proof -- one leaf the matcher library  *)
(*    recognizes (`store_same_twice`, nested inside the array built     *)
(*    above) composed via `Trans` with one leaf it does *not*           *)
(*    recognize (`select(const(c),i) = c`, `lemma_select_const` --      *)
(*    genuinely out of scope here, since no `const` operator is given   *)
(*    semantics by `the_interpretation`). `collect_unmatched` isolates   *)
(*    exactly the second leaf; `lemma_partial_proof_true` then proves   *)
(*    the whole composed equation true given *only* that one leftover   *)
(*    obligation -- not the first, already-matched, leaf.               *)
(* ----------------------------------------------------------------- *)

let c_c = c0 (konst "c" int_s)
let const_d : func_decl = { decl_name = "const"; domain = [int_s]; range = arr_s; interp = None; int_params = [] }
let const_c : expr = c1 const_d c_c

(* The two leaves below are chained via `Trans`, which requires the
   first leaf's target to be syntactically the second leaf's source;
   `mid` is that shared middle expression. *)
let mid : expr = c2 select_d const_c i_c  (* `select(const(c),i)`, sort `int_s` *)

(* Leaf 1 (matched, `select_store_same`): `select(store(fx,i,mid),i) = mid`.
   `mid` itself is a compound expression, not a named constant -- the
   matcher does not care what the matched `x` sub-expression *is*, only
   that it has the right sort, underlining that this is a genuine
   structural match, not a relabeling of a literal example. *)
let twice_s = c2 select_d (c3 store_d fx i_c mid) i_c
let twice_t = mid
let twice_leaf : proof = mk_rewrite_leaf twice_s twice_t

(* Leaf 2 (unmatched by design: `const` is left uninterpreted by
   `the_interpretation`, so none of the six matchers recognize this
   shape): `select(const(c),i) = c`, i.e. `Z3ArrayTheory.lemma_select_const`. *)
let select_const_s = mid
let select_const_t = c_c
let select_const_leaf : proof = mk_rewrite_leaf select_const_s select_const_t

let mixed_leaf : proof = Trans twice_leaf select_const_leaf

let lemma_mixed_leftover_is_exactly_select_const ()
  : Lemma (collect_unmatched mixed_leaf == [(select_const_s, select_const_t)])
  = assert (select_store_same_leaf_ok twice_s twice_t);
    assert_norm (try_match_leaf select_const_s select_const_t == false)

(* The whole composed equation, `select(store(fx,i,mid),i) = c`, is
   proved true given *only* the one genuinely-unmatched fact
   (`select(const(c),i) = c`) -- the already-matched `store_same`
   leaf above needs no further trust, matched or not. *)
let lemma_mixed_proof_true (rho:env value)
  : Lemma (requires (forall (rho':env value).
                      eval the_interpretation select_const_s rho' ==
                      eval the_interpretation select_const_t rho'))
          (ensures eval the_interpretation twice_s rho == eval the_interpretation select_const_t rho)
  = lemma_mixed_leftover_is_exactly_select_const ();
    assert (leftover_sound (collect_unmatched mixed_leaf));
    lemma_partial_proof_true mixed_leaf rho

