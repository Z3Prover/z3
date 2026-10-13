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
   denote. Eleven patterns are covered this way (§4):
   `s = s` for any syntactically-identical `expr` `s` (reflexivity --
   needs no theory lemma, no sort side condition, and holds for any
   interpretation/theory whatsoever), `select(store(a,i,x),i) = x`,
   `store(store(a,i,x),i,y) = store(a,i,y)`, `store(a,i,select(a,i)) =
   a` (`Z3ArrayTheory.lemma_select_store_same`/`lemma_store_same_twice`/
   `lemma_store_redundant`), `(a++b)++c = a++(b++c)`
   (`Z3SeqRewrites.lemma_concat_assoc`), `not(not(x)) = x`
   (`Z3BoolRewriter.not_not`), `bvand(y,y) = y`
   (`Z3BvRewriter.lemma_bvand_self`), `(= a b) = (= b a)` (`eq_symm`,
   symmetry of the new `op_eq` interpreted operator -- needs no theory
   lemma, just `Z3InterpretedProofChecker.lemma_value_eq_sym_symmetric`),
   `select(store(a,i,x),j) = select(a,j)` for `i <> j`
   (`Z3ArrayTheory.lemma_select_store_diff`, whenever `i`/`j` are
   themselves distinctly-named 0-ary uninterpreted Int constants --
   see §4i below for how the previously-unsatisfiable `i <> j` side
   condition is now discharged), `store(store(a,i,x),j,y) =
   store(store(a,j,y),i,x)` for `i <> j` (`store_commute`, §4j,
   `Z3ArrayTheory.lemma_store_commute` -- the index-swap twin of
   `select_store_diff`, discharged the same way, and the dominant
   previously-unmatched shape in the QF_AX benchmark corpus), and an
   arbitrary-length chain of nested `store`s against *any* reordering
   of the same `(index,value)` updates with pairwise-distinct indices
   (`store_perm`, §4k, `Z3ArrayTheory.lemma_apply_updates_set_eq` --
   `store_commute` is this theorem's `n = 2` special case).

   Not every `Rewrite` leaf fits one of these eleven schemas -- Z3's
   rewriters encode many more rewrite rules than this (or any single
   bounded) pattern library can realistically enumerate. Rather than
   either trusting the whole proof tree unconditionally
   (`all_leaves_sound`, the pre-existing baseline) or rejecting
   anything not recognized (`all_matched`, all-or-nothing, §6), §7
   adds a *partial* mode: `collect_unmatched` walks a proof tree and
   returns the exact list of `Rewrite` leaves none of the eleven
   matchers recognize, and `lemma_partial_proof_true` proves the whole
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

   Known limitation (documented, and now *fully* addressed by §4i/
   §4j/§4k for named constants *and* literal numerals -- see
   `provably_distinct` right before §4i): the companion patterns
   `select(store(a,i,x),j) = select(a,j)` and
   `store(store(a,i,x),j,y) = store(store(a,j,y),i,x)`, both for `i <>
   j` (`Z3ArrayTheory.lemma_select_store_diff`/`lemma_store_commute`),
   require a genuine semantic disequality `i <> j`, not just a shape
   fact. Under the old `uninterp_app` (every 0-ary constant of a sort
   denoted the *same* fixed value), this was unsatisfiable for *any*
   two named constants. `uninterp_app` now injects distinct
   `decl_name`s to distinct `VInt`s (`string_key`/
   `lemma_string_key_distinct`), and `Z3InterpretedProofChecker.fst`
   separately gives `true`/`false`/Int-numeral/BV-numeral *literals*
   real, name-independent denotations, so `provably_distinct`
   discharges `i <> j` whenever `i`/`j` are *either* two
   distinctly-named 0-ary uninterpreted Int constants *or* two
   literal numerals (Int or BV) with different decoded values --
   demonstrated on literals in §13 (`lit_ssd_leaf`/`lit_bv_leaf`).
   Compound index expressions (e.g.
   `i+1` vs `j`) are still out of reach -- a semantic disequality for
   those cannot be derived from syntax alone under this model -- and
   remain an unmatched, collected leaf.
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
    else if k = op_eq then
      (match f.domain with
       | [d1; d2] -> sort_eq d1 d2 && sort_eq f.range bool_s
       | _ -> false)
    else if k = op_true then f.domain = [] && sort_eq f.range bool_s
    else if k = op_false then f.domain = [] && sort_eq f.range bool_s
    else if k = op_num_int then f.domain = [] && sort_eq f.range int_s && length f.int_params = 1
    else if k = op_num_bv then f.domain = [] && sort_eq f.range bv_s && length f.int_params = 1
    else false (* some other interpreted op: not trusted by this file *)

let rec decls_ok (e:expr) : Tot bool (decreases e) =
  match e with
  | Var _ _ -> true
  | App f args -> decl_shape_ok f && decls_ok_args args
  | Quantifier _ _ _ body -> decls_ok body

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
  | Quantifier _ _ _ _ -> false

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
  if sort_eq srt bool_s then VBool? v
  else if sort_eq srt bv_s then VBV? v
  else if sort_eq srt seq_s then VSeq? v
  else if sort_eq srt arr_s then VArr? v
  else (* "Int" and anything else *) VInt? v

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
  = if sort_eq srt bool_s then ()
    else if sort_eq srt bv_s then ()
    else if sort_eq srt seq_s then ()
    else if sort_eq srt arr_s then ()
    else ()

(* Mirrors `uninterp_app`'s own case split (0-ary + Int-sorted gets an
   injective `string_key`-derived `VInt`; everything else falls back to
   `default_value`): both branches still only ever produce a `VInt`,
   so `shape_ok` holds unconditionally either way. *)
let lemma_uninterp_app_shape_ok (f:func_decl{is_uninterp_decl f}) (vs:list value)
  : Lemma (shape_ok (uninterp_app f vs) f.range)
  = match vs with
    | [] -> if sort_eq f.range (BaseSort "Int") then () else lemma_default_value_shape_ok f.range
    | _ -> lemma_default_value_shape_ok f.range

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
    | Quantifier _ _ _ _ -> () (* impossible: ruled out by `no_quant e` *)
    | App f args ->
      lemma_eval_shape_args args rho;
      let vs = eval_args the_interpretation args rho in
      (match f.interp with
       | None -> lemma_uninterp_app_shape_ok f vs
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
         else if k = op_eq then
           (match vs with
            | [a; b] -> ()
            | _ -> ())
         else if k = op_true then ()
         else if k = op_false then ()
         else if k = op_num_int then
           (match f.int_params with [v] -> () | _ -> ())
         else if k = op_num_bv then
           (match f.int_params with [v] -> () | _ -> ())
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
(* 4. The matcher *library*: eleven structural recognizers. Six are     *)
(*    one per already-proven rewrite-rule lemma that needs no semantic  *)
(*    side condition beyond shapes, and is expressible purely with the  *)
(*    six interpreted ops `Z3InterpretedProofChecker.fst` already gives *)
(*    real semantics to (`select`/`store`/`not`/`plus`/`bvand`/         *)
(*    `concat`, i.e. no new `const`/`ite`/`map` operator semantics is    *)
(*    added here). The seventh, reflexivity (`s = s`), needs no theory  *)
(*    lemma or interpreted op at all -- it is sound for *any* `expr`,    *)
(*    under *any* interpretation, by construction (see §4g below for    *)
(*    the justification). The eighth, `eq_symm` (§4h), needs only the   *)
(*    new `op_eq` operator's symmetry, no theory lemma. The ninth and    *)
(*    tenth, `select_store_diff` (§4i) and `store_commute` (§4j), *do*   *)
(*    need a genuine semantic side condition (`i <> j`), both           *)
(*    discharged via the same injective-naming model fix described in   *)
(*    the module docstring. The eleventh, `store_perm` (§4k),           *)
(*    generalizes `store_commute` to an arbitrary-length chain of       *)
(*    nested `store`s against any pairwise-distinct-index reordering.   *)
(*    Every leftover array/seq/bool/bv lemma                            *)
(*    this file does *not* match (`lemma_select_const`,                 *)
(*    `lemma_select_ite`, `lemma_select_lambda`, `lemma_lambda_eta`,     *)
(*    `lemma_select_map1/2`, `lemma_map2_store/const/lambda`,           *)
(*    `lemma_array_extensionality`, the `set_*` lemmas,                  *)
(*    `lemma_eq_const_*`, and anything from                              *)
(*    `Z3SeqAxioms`/`Z3SeqDerive`/`Z3ArithRewriter`/etc. not already     *)
(*    wired into `the_interpretation`) is not silently ignored: §5-6    *)
(*    below turn every `Rewrite` leaf that fails all eleven matchers    *)
(*    into an explicit, collected *leftover proof obligation* instead.  *)
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

#push-options "--z3rlimit 50"
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
#pop-options

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

(* 4g. Reflexivity: `s = t` (as *syntactically identical* `expr`
       values). Unlike the six theory-specific schemas above, this one
       needs no sort/shape side condition and no theory lemma at all:
       if a `Rewrite` leaf's two sides are literally the same `expr`,
       then `eval i s rho` and `eval i t rho` are the same application
       of `eval` to the same argument, so they are equal by plain
       reflexivity of `==` -- true for *any* interpretation `i`, *any*
       theory/sort, and *any* environment `rho`, not just the fixed
       `the_interpretation` this file otherwise targets. This covers
       `Rewrite` leaves Z3 emits for no-op normalization steps (the
       rewriter re-derives an already-fully-simplified term) and is
       the simplest possible instance of the general principle that a
       `Rewrite` leaf asserts an *equation*, and every equation is
       trivially valid when both sides denote the same term. *)

let reflexivity_leaf_ok (s t:expr) : bool = s = t

let lemma_reflexivity_leaf_sound (s t:expr)
  : Lemma (requires reflexivity_leaf_ok s t)
          (ensures all_leaves_sound the_interpretation (mk_rewrite_leaf s t))
  = let aux (rho:env value)
      : Lemma (eval the_interpretation s rho == eval the_interpretation t rho)
      = ()
    in
    FStar.Classical.forall_intro aux

(* 4h. `(= a b) = (= b a)` -- symmetry of equality, for *any* two
       same-sorted sub-expressions `a`/`b` (no theory lemma needed:
       `op_eq`'s denotation `value_eq_sym` is proved symmetric once,
       in `Z3InterpretedProofChecker.lemma_value_eq_sym_symmetric`).
       This is the `eq_symm` pattern: observed directly in Z3 proofs
       of `array-ext`-derived goals (orientation-swapped equality
       leaves), and sound for every sort this checker models. *)

let match_eq_symm (s t:expr) : option (expr & expr) =
  match s, t with
  | App f1 [a; b], App f2 [b'; a'] ->
    if Some? f1.interp && Some?.v f1.interp = op_eq &&
       Some? f2.interp && Some?.v f2.interp = op_eq &&
       a = a' && b = b'
    then Some (a, b)
    else None
  | _, _ -> None

let eq_symm_leaf_ok (s t:expr) : bool =
  match match_eq_symm s t with
  | None -> false
  | Some (a, b) ->
    wf s && wf t && closed s && closed t && decls_ok s && decls_ok t && no_quant s && no_quant t &&
    sort_eq (get_sort a) (get_sort b)

let lemma_eq_symm_leaf_sound (s t:expr)
  : Lemma (requires eq_symm_leaf_ok s t)
          (ensures all_leaves_sound the_interpretation (mk_rewrite_leaf s t))
  = match s, t with
    | App f1 [a; b], App f2 [b'; a'] ->
      assert (a = a' && b = b');
      let aux (rho:env value)
        : Lemma (eval the_interpretation s rho == eval the_interpretation t rho)
        = lemma_eval_shape a rho;
          lemma_eval_shape b rho;
          lemma_value_eq_sym_symmetric (eval the_interpretation a rho) (eval the_interpretation b rho)
      in
      FStar.Classical.forall_intro aux
    | _, _ -> ()

(* 4i. `select(store(a,i,x),j) = select(a,j)` for `i <> j` --
       `Z3ArrayTheory.lemma_select_store_diff`. This is the pattern the
       module docstring used to document as an unsupported "known
       limitation": its side condition `i <> j` is a genuine semantic
       fact, not just a shape fact, and is unsatisfiable for *any* two
       named constants under the *old* `uninterp_app` (every 0-ary
       constant of a sort denoted the *same* fixed value). Now that
       `uninterp_app` injects distinct `decl_name`s to distinct `VInt`s
       (`Z3InterpretedProofChecker.string_key`/
       `lemma_string_key_distinct`), this matcher can discharge `i <>
       j` whenever `i`/`j` are *themselves* distinctly-named, 0-ary
       uninterpreted Int constants -- a decidable, purely syntactic
       side condition. (Compound index expressions, e.g. `i+1` vs `j`,
       are still out of reach: they would need a semantic
       disequality proof this checker's model cannot derive from
       syntax alone, and remain an unmatched, collected leaf.) *)

let is_uninterp_const (e:expr) : bool =
  match e with
  | App f [] -> None? f.interp
  | _ -> false

let const_name (e:expr{is_uninterp_const e}) : string =
  match e with
  | App f [] -> f.decl_name

(* `provably_distinct` generalizes the single case above (two
   distinctly-named 0-ary *uninterpreted* Int constants) to *literal*
   constants as well: `true`/`false` (`op_true`/`op_false`), two Int
   numerals with different raw values (`op_num_int`), and two BV
   numerals with different *post-`bv32_value`-reduction* values
   (`op_num_bv` -- two different raw `int_params` can denote the same
   bit-vector mod 2^32, so distinctness must be decided on the
   reduced value, never the raw parameter). Unlike the
   uninterpreted-constant case (sound only because `Int` is an
   *infinite* sort -- see the module docstring's discussion of why
   the naming trick cannot be used for `Bool`/`BVn`), literal
   distinctness is sound for *any* sort, finite or not: a literal's
   denotation is a fixed, name-independent function of its own
   decoded payload (`interp_true`/`interp_false`/`interp_num_int`/
   `interp_num_bv`), not a free/symbolic choice, so two literals
   decoding to different payloads can never collide under any
   interpretation. *)

let is_bool_true_const (e:expr) : bool =
  match e with
  | App f [] -> Some? f.interp && Some?.v f.interp = op_true
  | _ -> false

let is_bool_false_const (e:expr) : bool =
  match e with
  | App f [] -> Some? f.interp && Some?.v f.interp = op_false
  | _ -> false

let is_int_num_const (e:expr) : bool =
  match e with
  | App f [] -> Some? f.interp && Some?.v f.interp = op_num_int && length f.int_params = 1
  | _ -> false

let int_num_value (e:expr{is_int_num_const e}) : int =
  match e with
  | App f [] -> List.Tot.hd f.int_params

let is_bv_num_const (e:expr) : bool =
  match e with
  | App f [] -> Some? f.interp && Some?.v f.interp = op_num_bv && length f.int_params = 1
  | _ -> false

let bv_num_value (e:expr{is_bv_num_const e}) : Z3BvTheory.bv 32 =
  match e with
  | App f [] -> bv32_value (List.Tot.hd f.int_params)

(* The uninterpreted-constant disjunct additionally requires an
   `Int`-sorted range: `uninterp_app` only injects a name-dependent
   (hence provably-distinct-by-name) `VInt` for 0-ary, `Int`-sorted
   declarations -- every other uninterpreted constant (e.g. two
   differently-named `Bool` constants) gets the *same*
   name-independent `default_value`, so two such constants can
   *not* be assumed distinct. *)
let is_int_uninterp_const (e:expr) : bool =
  is_uninterp_const e && sort_eq (get_sort e) int_s

let provably_distinct (a b:expr) : bool =
  (is_int_uninterp_const a && is_int_uninterp_const b && const_name a <> const_name b) ||
  (is_bool_true_const a && is_bool_false_const b) ||
  (is_bool_false_const a && is_bool_true_const b) ||
  (is_int_num_const a && is_int_num_const b && int_num_value a <> int_num_value b) ||
  (is_bv_num_const a && is_bv_num_const b && bv_num_value a <> bv_num_value b)

(* The soundness bridge: whenever `provably_distinct a b` holds (and
   `a`/`b` are themselves well-formed, closed, `decls_ok`,
   quantifier-free sub-expressions -- the same shape hypotheses
   `lemma_eval_shape` needs), their *denotations* under
   `the_interpretation` actually differ. This is the one lemma every
   matcher needing a semantic index-disequality side condition
   (`select_store_diff`, `store_commute`, `store_perm`) now calls,
   replacing the previous ad-hoc inline `lemma_string_key_distinct`
   invocation at each call site. *)
let lemma_provably_distinct_sound (a b:expr) (rho:env value)
  : Lemma (requires provably_distinct a b /\
                    wf a /\ closed a /\ decls_ok a /\ no_quant a /\
                    wf b /\ closed b /\ decls_ok b /\ no_quant b)
          (ensures eval the_interpretation a rho =!= eval the_interpretation b rho)
  = if is_int_uninterp_const a && is_int_uninterp_const b && const_name a <> const_name b then
      (match a, b with
       | App fa [], App fb [] -> lemma_string_key_distinct fa.decl_name fb.decl_name
       | _, _ -> ())
    else ()

let match_select_store_diff (s t:expr) : option (expr & expr & expr & expr) =
  match s, t with
  | App f_sel1 [App f_sto [a; i; x]; j], App f_sel2 [a'; j'] ->
    if Some? f_sel1.interp && Some?.v f_sel1.interp = op_select &&
       Some? f_sto.interp && Some?.v f_sto.interp = op_store &&
       Some? f_sel2.interp && Some?.v f_sel2.interp = op_select &&
       a = a' && j = j'
    then Some (a, i, x, j)
    else None
  | _, _ -> None

let select_store_diff_leaf_ok (s t:expr) : bool =
  match match_select_store_diff s t with
  | None -> false
  | Some (a, i, x, j) ->
    wf s && wf t && closed s && closed t && decls_ok s && decls_ok t && no_quant s && no_quant t &&
    sort_eq (get_sort a) arr_s && sort_eq (get_sort i) int_s &&
    sort_eq (get_sort x) int_s && sort_eq (get_sort j) int_s &&
    provably_distinct i j

#push-options "--z3rlimit 80"
let lemma_select_store_diff_leaf_sound (s t:expr)
  : Lemma (requires select_store_diff_leaf_ok s t)
          (ensures all_leaves_sound the_interpretation (mk_rewrite_leaf s t))
  = match s, t with
    | App f_sel1 [App f_sto [a; i; x]; j], App f_sel2 [a'; j'] ->
      assert (a = a' && j = j');
      let aux (rho:env value)
        : Lemma (eval the_interpretation s rho == eval the_interpretation t rho)
        = lemma_eval_shape a rho;
          lemma_eval_shape i rho;
          lemma_eval_shape x rho;
          lemma_eval_shape j rho;
          lemma_provably_distinct_sound i j rho;
          (match eval the_interpretation a rho, eval the_interpretation i rho,
                 eval the_interpretation x rho, eval the_interpretation j rho with
           | VArr av, VInt iv, VInt xv, VInt jv ->
             Z3ArrayTheory.lemma_select_store_diff av iv jv xv
           | _, _, _, _ -> ())
      in
      FStar.Classical.forall_intro aux
    | _, _ -> ()
#pop-options

(* 4j. `store(store(a,i,x),j,y) = store(store(a,j,y),i,x)` for
       `i <> j` -- `Z3ArrayTheory.lemma_store_commute`, the index-swap
       twin of `select_store_diff` (§4i): same genuine semantic side
       condition `i <> j`, discharged the same way (`i`/`j` must be
       two distinctly-named 0-ary uninterpreted Int constants, via
       the injective-naming `uninterp_app`/`string_key` model fix).
       This was the dominant unmatched shape in the QF_AX benchmark
       corpus (`storecomm_*`, multi-level store-commutativity chains
       collapse to repeated one-step applications of this rule). *)

let match_store_commute (s t:expr) : option (expr & expr & expr & expr & expr) =
  match s, t with
  | App f_sto1 [App f_sto2 [a; i; x]; j; y], App f_sto3 [App f_sto4 [a'; j'; y']; i'; x'] ->
    if Some? f_sto1.interp && Some?.v f_sto1.interp = op_store &&
       Some? f_sto2.interp && Some?.v f_sto2.interp = op_store &&
       Some? f_sto3.interp && Some?.v f_sto3.interp = op_store &&
       Some? f_sto4.interp && Some?.v f_sto4.interp = op_store &&
       a = a' && i = i' && j = j' && x = x' && y = y'
    then Some (a, i, x, j, y)
    else None
  | _, _ -> None

let store_commute_leaf_ok (s t:expr) : bool =
  match match_store_commute s t with
  | None -> false
  | Some (a, i, x, j, y) ->
    wf s && wf t && closed s && closed t && decls_ok s && decls_ok t && no_quant s && no_quant t &&
    sort_eq (get_sort a) arr_s && sort_eq (get_sort i) int_s &&
    sort_eq (get_sort x) int_s && sort_eq (get_sort j) int_s && sort_eq (get_sort y) int_s &&
    provably_distinct i j

#push-options "--z3rlimit 100"
let lemma_store_commute_leaf_sound (s t:expr)
  : Lemma (requires store_commute_leaf_ok s t)
          (ensures all_leaves_sound the_interpretation (mk_rewrite_leaf s t))
  = match s, t with
    | App f_sto1 [App f_sto2 [a; i; x]; j; y], App f_sto3 [App f_sto4 [a'; j'; y']; i'; x'] ->
      assert (a = a' && i = i' && j = j' && x = x' && y = y');
      let aux (rho:env value)
        : Lemma (eval the_interpretation s rho == eval the_interpretation t rho)
        = lemma_eval_shape a rho;
          lemma_eval_shape i rho;
          lemma_eval_shape x rho;
          lemma_eval_shape j rho;
          lemma_eval_shape y rho;
          lemma_provably_distinct_sound i j rho;
          (match eval the_interpretation a rho, eval the_interpretation i rho,
                 eval the_interpretation x rho, eval the_interpretation j rho,
                 eval the_interpretation y rho with
           | VArr av, VInt iv, VInt xv, VInt jv, VInt yv ->
             Z3ArrayTheory.lemma_store_commute av iv jv xv yv
           | _, _, _, _, _ -> ())
      in
      FStar.Classical.forall_intro aux
    | _, _ -> ()
#pop-options

(* 4k. **The general multi-level store-permutation theorem.** Rather
       than a fixed two-level swap (`store_commute`, §4j), this matcher
       recognizes an arbitrary-length chain
       `store(store(...store(a,i1,x1)...),i_{n-1},x_{n-1}),in,xn)`
       against *any* reordering of the same `(index,value)` updates
       with pairwise-distinct indices, via
       `Z3ArrayTheory.lemma_apply_updates_set_eq`. `store_commute` is
       the `n = 2` special case of this theorem. *)

/// Peel nested `store` applications off the *outside* of `e`,
/// collecting each layer's `(index, value)` pair. The outermost
/// `store` is applied *last*, so recursing into the base array first
/// and appending `(i,x)` at the *end* of the recursive result matches
/// `Z3ArrayTheory.apply_updates`'s left-to-right, head-applied-first
/// fold convention. A non-`store` node is the chain's base, with no
/// pairs of its own.
let rec flatten_store (e:expr) : Tot (expr & list (expr & expr)) (decreases e) =
  match e with
  | App f [a; i; x] ->
    if Some? f.interp && Some?.v f.interp = op_store
    then let (base, us) = flatten_store a in (base, us @ [(i, x)])
    else (e, [])
  | _ -> (e, [])

/// Every `(index,value)` pair in a flattened update list is itself a
/// well-formed, closed, quantifier-free Int-sorted pair of
/// sub-expressions -- the per-pair well-formedness obligation
/// `lemma_eval_shape` needs to be invokable at each level.
let pairs_wf (us:list (expr & expr)) : prop =
  forall (p:(expr & expr)). mem p us ==>
    wf (fst p) /\ closed (fst p) /\ decls_ok (fst p) /\ no_quant (fst p) /\ sort_eq (get_sort (fst p)) int_s /\
    wf (snd p) /\ closed (snd p) /\ decls_ok (snd p) /\ no_quant (snd p) /\ sort_eq (get_sort (snd p)) int_s

/// `i` is `provably_distinct` (§4i's generalized distinctness
/// recognizer -- named constants *or* literal numerals) from the
/// index of every pair in `us` (a one-against-the-rest check; folded
/// over all positions by `pairwise_distinct_keys` below to get a
/// full all-pairs check).
let rec all_const_distinct_from (i:expr) (us:list (expr & expr)) : Tot bool (decreases us) =
  match us with
  | [] -> true
  | (j, _) :: rest ->
    provably_distinct i j &&
    all_const_distinct_from i rest

/// Every index in `us` is a distinctly-named uninterpreted constant
/// from every *other* index in `us` -- the syntactic side condition
/// generalizing `select_store_diff`/`store_commute`'s single `i <> j`
/// to an arbitrary-length chain.
let rec pairwise_distinct_keys (us:list (expr & expr)) : Tot bool (decreases us) =
  match us with
  | [] -> true
  | (i, _) :: rest -> all_const_distinct_from i rest && pairwise_distinct_keys rest

let rec all_mem (us1 us2:list (expr & expr)) : Tot bool (decreases us1) =
  match us1 with
  | [] -> true
  | p :: rest -> mem p us2 && all_mem rest us2

/// `us1` and `us2` contain exactly the same set of `(index,value)`
/// pairs (order- and multiplicity-independent, since
/// `pairwise_distinct_keys` below separately rules out duplicate
/// indices).
let same_update_set (us1 us2:list (expr & expr)) : bool =
  all_mem us1 us2 && all_mem us2 us1

let match_store_perm (s t:expr) : option (expr & list (expr & expr) & list (expr & expr)) =
  let (base_s, us_s) = flatten_store s in
  let (base_t, us_t) = flatten_store t in
  if base_s = base_t && length us_s >= 2 && length us_s = length us_t &&
     pairwise_distinct_keys us_s && pairwise_distinct_keys us_t &&
     same_update_set us_s us_t
  then Some (base_s, us_s, us_t)
  else None

let store_perm_leaf_ok (s t:expr) : bool =
  match match_store_perm s t with
  | None -> false
  | Some (base, us_s, us_t) ->
    wf s && wf t && closed s && closed t && decls_ok s && decls_ok t && no_quant s && no_quant t

/// Evaluate a list of `(index,value)` expression pairs into the
/// `(int & int)` pairs `Z3ArrayTheory.apply_updates` folds over.
let rec eval_pairs (rho:env value) (us:list (expr & expr)) : Tot (list (int & int)) (decreases us) =
  match us with
  | [] -> []
  | (i, x) :: rest ->
    (match eval the_interpretation i rho, eval the_interpretation x rho with
     | VInt iv, VInt xv -> (iv, xv) :: eval_pairs rho rest
     | _, _ -> (0, 0) :: eval_pairs rho rest)

let rec lemma_mem_append_elim (#a:eqtype) (x:a) (l1 l2:list a)
  : Lemma (requires mem x (l1 @ l2)) (ensures mem x l1 \/ mem x l2) (decreases l1)
  = match l1 with
    | [] -> ()
    | h :: t -> if h = x then () else lemma_mem_append_elim x t l2

/// Propagates `wf`/`closed`/`decls_ok`/`no_quant` (and, via
/// `decl_shape_ok`'s fixed `op_store` domain, the sort facts
/// `pairs_wf` needs) from a store-chain expression down to its
/// flattened base and every `(index,value)` pair -- all for free by
/// unfolding `wf`/`decls_ok`'s own compositional definitions one
/// `App` layer at a time, mirroring `flatten_store`'s recursion.
/// The one structural fact `lemma_flatten_store_wf`'s base case needs
/// but cannot derive on its own: if `e`'s chain has peeled off at
/// least one `store` layer, `e` itself must have taken the "it *is* a
/// `store` application" branch of `flatten_store`'s own case split
/// (the other two branches always return an *empty* pair list), so
/// `decls_ok`'s `op_store` domain/range fact (`decl_shape_ok`) gives
/// `sort_eq (get_sort e) arr_s` for free. A direct, non-recursive
/// unfolding of `flatten_store` once -- no induction needed.
let lemma_flatten_nonempty_sort (e:expr)
  : Lemma (requires decls_ok e /\ Cons? (snd (flatten_store e)))
          (ensures sort_eq (get_sort e) arr_s)
  = match e with
    | App f [a; i; x] -> ()
    | _ -> ()

#push-options "--z3rlimit 60"
let rec lemma_flatten_store_wf (s:expr)
  : Lemma (requires wf s /\ closed s /\ decls_ok s /\ no_quant s /\ sort_eq (get_sort s) arr_s)
          (ensures (let (base, us) = flatten_store s in
                       wf base /\ closed base /\ decls_ok base /\ no_quant base /\
                       sort_eq (get_sort base) arr_s /\ pairs_wf us))
          (decreases s)
  = match s with
    | App f [a; i; x] ->
      if Some? f.interp && Some?.v f.interp = op_store then begin
        lemma_flatten_store_wf a;
        let (base, us_a) = flatten_store a in
        let aux (p:(expr & expr))
          : Lemma (requires mem p (us_a @ [(i, x)]))
                     (ensures wf (fst p) /\ closed (fst p) /\ decls_ok (fst p) /\ no_quant (fst p) /\
                              sort_eq (get_sort (fst p)) int_s /\
                              wf (snd p) /\ closed (snd p) /\ decls_ok (snd p) /\ no_quant (snd p) /\
                              sort_eq (get_sort (snd p)) int_s)
          = lemma_mem_append_elim p us_a [(i, x)]
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
      end
      else ()
    | _ -> ()
#pop-options

/// `eval_pairs` commutes with list append -- needed because
/// `flatten_store`'s recursive case builds `us_a @ [(i,x)]` while
/// `apply_updates`'s connecting lemma
/// (`Z3ArrayTheory.lemma_apply_updates_append`) is stated over the
/// already-*evaluated* `eval_pairs rho us_a @ [(iv,xv)]`.
let rec lemma_eval_pairs_append (rho:env value) (us1 us2:list (expr & expr))
  : Lemma (ensures eval_pairs rho (us1 @ us2) == eval_pairs rho us1 @ eval_pairs rho us2)
          (decreases us1)
  = match us1 with
    | [] -> ()
    | p :: rest -> lemma_eval_pairs_append rho rest us2

/// Connects `eval` of a genuine store-chain expression to
/// `Z3ArrayTheory.apply_updates`: `eval s rho` denotes
/// `VArr (apply_updates a0 (eval_pairs rho us))` whenever `eval base
/// rho = VArr a0`, where `(base, us) = flatten_store s`. Proved by
/// induction mirroring `flatten_store`'s own recursion, using
/// `Z3ArrayTheory.lemma_apply_updates_append` to connect one more
/// peeled `store` layer to one more folded update.
#push-options "--z3rlimit 100"
let rec lemma_eval_store_chain (s:expr) (rho:env value)
  : Lemma (requires wf s /\ closed s /\ decls_ok s /\ no_quant s)
          (ensures (let (base, us) = flatten_store s in
                       match eval the_interpretation base rho with
                       | VArr a0 -> eval the_interpretation s rho == VArr (Z3ArrayTheory.apply_updates a0 (eval_pairs rho us))
                       | _ -> True))
          (decreases s)
  = match s with
    | App f [a; i; x] ->
      if Some? f.interp && Some?.v f.interp = op_store then begin
        lemma_eval_shape i rho;
        lemma_eval_shape x rho;
        lemma_eval_store_chain a rho;
        let (base, us_a) = flatten_store a in
        (match eval the_interpretation base rho with
         | VArr a0 ->
           (match eval the_interpretation i rho, eval the_interpretation x rho with
            | VInt iv, VInt xv ->
              Z3ArrayTheory.lemma_apply_updates_append a0 (eval_pairs rho us_a) iv xv;
              lemma_eval_pairs_append rho us_a [(i, x)]
            | _, _ -> ())
         | _ -> ())
      end
      else ()
    | _ -> ()
#pop-options

(* The semantic (evaluated-`int`-pair) counterpart of
   `pairwise_distinct_keys`/`same_update_set`, bridged to the
   syntactic checks via `lemma_string_key_distinct` (the same
   injective-naming fact `select_store_diff`/`store_commute` already
   rely on) -- needed to supply
   `Z3ArrayTheory.lemma_apply_updates_set_eq`'s `key_distinct_hyp`/
   `same_set` witnesses. *)

let rec all_index_distinct_from (k:int) (ps:list (int & int)) : Tot bool (decreases ps) =
  match ps with
  | [] -> true
  | (i, _) :: rest -> k <> i && all_index_distinct_from k rest

let rec distinct_indices (ps:list (int & int)) : Tot bool (decreases ps) =
  match ps with
  | [] -> true
  | (i, _) :: rest -> all_index_distinct_from i rest && distinct_indices rest

let rec lemma_all_index_distinct_from_not_mem (k:int) (ps:list (int & int))
  : Lemma (requires all_index_distinct_from k ps)
          (ensures forall (y:int). ~(mem (k, y) ps))
          (decreases ps)
  = match ps with
    | [] -> ()
    | (i, _) :: rest -> lemma_all_index_distinct_from_not_mem k rest

let rec lemma_distinct_indices_unique (ps:list (int & int)) (k x1 x2:int)
  : Lemma (requires distinct_indices ps /\ mem (k, x1) ps /\ mem (k, x2) ps)
          (ensures x1 == x2)
          (decreases ps)
  = match ps with
    | (i, x) :: rest ->
      if i = k
      then lemma_all_index_distinct_from_not_mem k rest
      else lemma_distinct_indices_unique rest k x1 x2

let rec lemma_all_const_distinct_from_eval (i:expr) (iv:int) (rest:list (expr & expr)) (rho:env value)
  : Lemma (requires all_const_distinct_from i rest /\ pairs_wf rest /\
                        wf i /\ closed i /\ decls_ok i /\ no_quant i /\
                        sort_eq (get_sort i) int_s /\
                        eval the_interpretation i rho == VInt iv)
          (ensures all_index_distinct_from iv (eval_pairs rho rest))
          (decreases rest)
  = match rest with
    | [] -> ()
    | (j, y) :: rest' ->
      lemma_all_const_distinct_from_eval i iv rest' rho;
      assert (mem (j, y) rest);
      assert (wf j /\ closed j /\ decls_ok j /\ no_quant j /\ sort_eq (get_sort j) int_s /\
              wf y /\ closed y /\ decls_ok y /\ no_quant y);
      lemma_eval_shape j rho;
      lemma_eval_shape y rho;
      lemma_provably_distinct_sound i j rho;
      (match eval the_interpretation i rho, eval the_interpretation j rho with
       | VInt iv', VInt jv -> assert (iv == iv' /\ iv <> jv)
       | _, _ -> ())

#push-options "--z3rlimit 60"
let rec lemma_eval_pairs_distinct_indices (us:list (expr & expr)) (rho:env value)
  : Lemma (requires pairwise_distinct_keys us /\ pairs_wf us)
          (ensures distinct_indices (eval_pairs rho us))
          (decreases us)
  = match us with
    | [] -> ()
    | (i, x) :: rest ->
      lemma_eval_pairs_distinct_indices rest rho;
      assert (mem (i, x) ((i, x) :: rest));
      assert (wf i /\ closed i /\ decls_ok i /\ no_quant i /\ sort_eq (get_sort i) int_s /\
              wf x /\ closed x /\ decls_ok x /\ no_quant x);
      lemma_eval_shape i rho;
      lemma_eval_shape x rho;
      (match eval the_interpretation i rho with
       | VInt iv -> lemma_all_const_distinct_from_eval i iv rest rho
       | _ -> ())
#pop-options

let store_perm_distinct (us:list (expr & expr){pairwise_distinct_keys us /\ pairs_wf us}) (rho:env value)
  : Z3ArrayTheory.key_distinct_hyp int int (eval_pairs rho us)
  = lemma_eval_pairs_distinct_indices us rho;
    fun (k:int) (x1:int) (x2:int) -> lemma_distinct_indices_unique (eval_pairs rho us) k x1 x2

let rec lemma_mem_eval_pairs_intro (us:list (expr & expr)) (rho:env value) (i x:expr) (iv xv:int)
  : Lemma (requires pairs_wf us /\ mem (i, x) us /\
                        eval the_interpretation i rho == VInt iv /\ eval the_interpretation x rho == VInt xv)
          (ensures mem (iv, xv) (eval_pairs rho us))
          (decreases us)
  = match us with
    | (i', x') :: rest ->
      if i' = i && x' = x then ()
      else begin
        assert (mem (i', x') ((i', x') :: rest));
        assert (wf i' /\ closed i' /\ decls_ok i' /\ no_quant i' /\
                wf x' /\ closed x' /\ decls_ok x' /\ no_quant x');
        lemma_eval_shape i' rho;
        lemma_eval_shape x' rho;
        lemma_mem_eval_pairs_intro rest rho i x iv xv
      end

let rec lemma_eval_pairs_mem_transfer (us_s us_t:list (expr & expr)) (rho:env value) (k x:int)
  : Lemma (requires pairs_wf us_s /\ pairs_wf us_t /\ all_mem us_s us_t /\ mem (k, x) (eval_pairs rho us_s))
          (ensures mem (k, x) (eval_pairs rho us_t))
          (decreases us_s)
  = match us_s with
    | (i, xe) :: rest ->
      assert (mem (i, xe) ((i, xe) :: rest));
      assert (wf i /\ closed i /\ decls_ok i /\ no_quant i /\
              wf xe /\ closed xe /\ decls_ok xe /\ no_quant xe);
      lemma_eval_shape i rho;
      lemma_eval_shape xe rho;
      (match eval the_interpretation i rho, eval the_interpretation xe rho with
       | VInt iv, VInt xv ->
         if iv = k && xv = x
         then lemma_mem_eval_pairs_intro us_t rho i xe iv xv
         else lemma_eval_pairs_mem_transfer rest us_t rho k x
       | _, _ -> ())

let store_perm_same_set
    (us_s us_t:list (expr & expr){pairs_wf us_s /\ pairs_wf us_t /\ all_mem us_s us_t /\ all_mem us_t us_s})
    (rho:env value) (p:(int & int))
  : Lemma (mem p (eval_pairs rho us_s) <==> mem p (eval_pairs rho us_t))
  = let (k, x) = p in
    let f1 () : Lemma (requires mem (k, x) (eval_pairs rho us_s)) (ensures mem (k, x) (eval_pairs rho us_t))
      = lemma_eval_pairs_mem_transfer us_s us_t rho k x
    in
    let f2 () : Lemma (requires mem (k, x) (eval_pairs rho us_t)) (ensures mem (k, x) (eval_pairs rho us_s))
      = lemma_eval_pairs_mem_transfer us_t us_s rho k x
    in
    FStar.Classical.move_requires f1 ();
    FStar.Classical.move_requires f2 ()

#push-options "--z3rlimit 150"
let lemma_store_perm_leaf_sound (s t:expr)
  : Lemma (requires store_perm_leaf_ok s t)
          (ensures all_leaves_sound the_interpretation (mk_rewrite_leaf s t))
  = match match_store_perm s t with
    | Some (base, us_s, us_t) ->
      lemma_flatten_nonempty_sort s;
      lemma_flatten_nonempty_sort t;
      lemma_flatten_store_wf s;
      lemma_flatten_store_wf t;
      let aux (rho:env value)
        : Lemma (eval the_interpretation s rho == eval the_interpretation t rho)
        = lemma_eval_shape base rho;
          lemma_eval_store_chain s rho;
          lemma_eval_store_chain t rho;
          (match eval the_interpretation base rho with
           | VArr a0 ->
                let same_set = store_perm_same_set us_s us_t rho in
                let distinct_s = store_perm_distinct us_s rho in
                let distinct_t = store_perm_distinct us_t rho in
                Z3ArrayTheory.lemma_apply_updates_set_eq a0 (eval_pairs rho us_s) (eval_pairs rho us_t)
                                                          same_set distinct_s distinct_t
           | _ -> ())
      in
      FStar.Classical.forall_intro aux
    | None -> ()
#pop-options

(* ----------------------------------------------------------------- *)
(* 5. The combinator: try every matcher above in turn, and the          *)
(*    corresponding "matched implies sound" lemma (a case split over    *)
(*    the eleven, invoking whichever matcher actually fired).           *)
(* ----------------------------------------------------------------- *)

let try_match_leaf (s t:expr) : bool =
  reflexivity_leaf_ok s t ||
  select_store_same_leaf_ok s t ||
  store_same_twice_leaf_ok s t ||
  store_redundant_leaf_ok s t ||
  concat_assoc_leaf_ok s t ||
  not_not_leaf_ok s t ||
  bvand_self_leaf_ok s t ||
  eq_symm_leaf_ok s t ||
  select_store_diff_leaf_ok s t ||
  store_commute_leaf_ok s t ||
  store_perm_leaf_ok s t

let lemma_try_match_leaf_sound (s t:expr)
  : Lemma (requires try_match_leaf s t)
          (ensures all_leaves_sound the_interpretation (mk_rewrite_leaf s t))
  = if reflexivity_leaf_ok s t then lemma_reflexivity_leaf_sound s t
    else if select_store_same_leaf_ok s t then lemma_select_store_same_leaf_sound s t
    else if store_same_twice_leaf_ok s t then lemma_store_same_twice_leaf_sound s t
    else if store_redundant_leaf_ok s t then lemma_store_redundant_leaf_sound s t
    else if concat_assoc_leaf_ok s t then lemma_concat_assoc_leaf_sound s t
    else if not_not_leaf_ok s t then lemma_not_not_leaf_sound s t
    else if bvand_self_leaf_ok s t then lemma_bvand_self_leaf_sound s t
    else if eq_symm_leaf_ok s t then lemma_eq_symm_leaf_sound s t
    else if select_store_diff_leaf_ok s t then lemma_select_store_diff_leaf_sound s t
    else if store_commute_leaf_ok s t then lemma_store_commute_leaf_sound s t
    else lemma_store_perm_leaf_sound s t

(* ----------------------------------------------------------------- *)
(* 6. "Fully matched" mode: a decidable whole-proof-tree checker         *)
(*    mirroring `all_leaves_sound`'s own recursion, requiring *every*    *)
(*    `Rewrite` leaf to fit one of the eleven schemas above.            *)
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

(* ----------------------------------------------------------------- *)
(* 10. Demonstration 3: `select_store_diff` and `eq_symm`, the two       *)
(*     matchers added by the injective-naming model fix. `j_c`/`i_c`     *)
(*     are two *distinctly-named* 0-ary Int constants, so `select(      *)
(*     store(a_c,i_c,x_c),j_c) = select(a_c,j_c)` is matched (the        *)
(*     previously-documented "Known limitation"), and `(=  i_c j_c) =    *)
(*     (= j_c i_c)` is matched by `eq_symm`.                              *)
(* ----------------------------------------------------------------- *)

let a_c2 = c0 (konst "a2" arr_s)
let j_c  = c0 (konst "j" int_s)

let ssd_s : expr = c2 select_d (c3 store_d a_c2 i_c x_c) j_c
let ssd_t : expr = c2 select_d a_c2 j_c
let ssd_leaf : proof = mk_rewrite_leaf ssd_s ssd_t

let lemma_ssd_leaf_matched ()
  : Lemma (all_matched ssd_leaf)
  = ()

let lemma_ssd_leaf_true (rho:env value)
  : Lemma (eval the_interpretation ssd_s rho == eval the_interpretation ssd_t rho)
  = lemma_ssd_leaf_matched ();
    lemma_matched_proof_true ssd_leaf rho

let eq_d : func_decl = { decl_name = "="; domain = [int_s; int_s]; range = bool_s; interp = Some op_eq; int_params = [] }
let eqsym_s : expr = c2 eq_d i_c j_c
let eqsym_t : expr = c2 eq_d j_c i_c
let eqsym_leaf : proof = mk_rewrite_leaf eqsym_s eqsym_t

let lemma_eqsym_leaf_matched ()
  : Lemma (all_matched eqsym_leaf)
  = ()

let lemma_eqsym_leaf_true (rho:env value)
  : Lemma (eval the_interpretation eqsym_s rho == eval the_interpretation eqsym_t rho)
  = lemma_eqsym_leaf_matched ();
    lemma_matched_proof_true eqsym_leaf rho

(* ----------------------------------------------------------------- *)
(* 11. Demonstration 4: `store_commute`, the index-swap twin of          *)
(*     `select_store_diff` added afterwards. `i_c`/`j_c` are the same    *)
(*     two distinctly-named 0-ary Int constants, so                      *)
(*     `store(store(a_c2,i_c,x_c),j_c,y_c) =                             *)
(*     store(store(a_c2,j_c,y_c),i_c,x_c)` is matched -- the dominant     *)
(*     previously-unmatched shape in the QF_AX benchmark corpus          *)
(*     (`storecomm_*`).                                                  *)
(* ----------------------------------------------------------------- *)

let sc_s : expr = c3 store_d (c3 store_d a_c2 i_c x_c) j_c y_c
let sc_t : expr = c3 store_d (c3 store_d a_c2 j_c y_c) i_c x_c
let sc_leaf : proof = mk_rewrite_leaf sc_s sc_t

let lemma_sc_leaf_matched ()
  : Lemma (all_matched sc_leaf)
  = ()

let lemma_sc_leaf_true (rho:env value)
  : Lemma (eval the_interpretation sc_s rho == eval the_interpretation sc_t rho)
  = lemma_sc_leaf_matched ();
    lemma_matched_proof_true sc_leaf rho

(* ----------------------------------------------------------------- *)
(* 12. Demonstration 5: `store_perm`, the general multi-level           *)
(*     store-permutation theorem (§4k) that `store_commute` is the      *)
(*     `n = 2` special case of. `i_c`/`j_c`/`k_c` are three              *)
(*     distinctly-named 0-ary Int constants, so a *three*-level chain   *)
(*     `store(store(store(a_c2,i_c,x_c),j_c,y_c),k_c,z_c)` is matched    *)
(*     against *two* different reorderings of the same three updates:   *)
(*     `store(store(store(a_c2,k_c,z_c),i_c,x_c),j_c,y_c)` (a cyclic     *)
(*     rotation) and `store(store(store(a_c2,j_c,y_c),k_c,z_c),i_c,x_c)` *)
(*     (the other cyclic rotation) -- neither of which is a single       *)
(*     adjacent-pair swap, so `store_commute` alone could not have       *)
(*     matched either. *)
(* ----------------------------------------------------------------- *)

let k_c = c0 (konst "k" int_s)
let z_c = c0 (konst "z" int_s)

let sp3_base : expr = c3 store_d (c3 store_d (c3 store_d a_c2 i_c x_c) j_c y_c) k_c z_c
let sp3_rot1 : expr = c3 store_d (c3 store_d (c3 store_d a_c2 k_c z_c) i_c x_c) j_c y_c
let sp3_rot2 : expr = c3 store_d (c3 store_d (c3 store_d a_c2 j_c y_c) k_c z_c) i_c x_c

let sp3_leaf_1 : proof = mk_rewrite_leaf sp3_base sp3_rot1
let sp3_leaf_2 : proof = mk_rewrite_leaf sp3_base sp3_rot2

(* `provably_distinct`'s 5-way disjunction (vs. the single
   named-constant case these demos previously decided) needs more
   fuel to unfold through at proof time than the default. *)
#push-options "--z3rlimit 150"
let lemma_sp3_leaf_1_matched ()
  : Lemma (all_matched sp3_leaf_1)
  = ()

let lemma_sp3_leaf_2_matched ()
  : Lemma (all_matched sp3_leaf_2)
  = ()
#pop-options

let lemma_sp3_leaf_1_true (rho:env value)
  : Lemma (eval the_interpretation sp3_base rho == eval the_interpretation sp3_rot1 rho)
  = lemma_sp3_leaf_1_matched ();
    lemma_matched_proof_true sp3_leaf_1 rho

let lemma_sp3_leaf_2_true (rho:env value)
  : Lemma (eval the_interpretation sp3_base rho == eval the_interpretation sp3_rot2 rho)
  = lemma_sp3_leaf_2_matched ();
    lemma_matched_proof_true sp3_leaf_2 rho

(* ----------------------------------------------------------------- *)
(* 13. Demonstration 6: `provably_distinct` on *literal* constants,     *)
(*     not just distinctly-named uninterpreted ones. `num 3`/`num 5`   *)
(*     are two `op_num_int` literal applications with different raw     *)
(*     `int_params`, so `select(store(a_c2,num3,x_c),num5) =            *)
(*     select(a_c2,num5)` is matched by `select_store_diff` purely      *)
(*     from the two literals' *values*, with no name-based reasoning    *)
(*     (`lemma_string_key_distinct`) involved at all -- exercising the   *)
(*     `is_int_num_const`/`int_num_value` disjunct of `provably_distinct`*)
(*     that §4i/§4j's demos (`ssd_leaf`/`sc_leaf`, named constants only) *)
(*     never touch. A second instance, `bv3`/`bv5` (`op_num_bv`),       *)
(*     shows the same for bit-vector numerals (compared *post*          *)
(*     `bv32_value` reduction).                                         *)
(* ----------------------------------------------------------------- *)

let num_d (v:int) : func_decl =
  { decl_name = "num"; domain = []; range = int_s; interp = Some op_num_int; int_params = [v] }
let num3 : expr = c0 (num_d 3)
let num5 : expr = c0 (num_d 5)

let lit_ssd_s : expr = c2 select_d (c3 store_d a_c2 num3 x_c) num5
let lit_ssd_t : expr = c2 select_d a_c2 num5
let lit_ssd_leaf : proof = mk_rewrite_leaf lit_ssd_s lit_ssd_t

let lemma_lit_ssd_leaf_matched ()
  : Lemma (all_matched lit_ssd_leaf)
  = ()

let lemma_lit_ssd_leaf_true (rho:env value)
  : Lemma (eval the_interpretation lit_ssd_s rho == eval the_interpretation lit_ssd_t rho)
  = lemma_lit_ssd_leaf_matched ();
    lemma_matched_proof_true lit_ssd_leaf rho

let bv_d (v:int) : func_decl =
  { decl_name = "bvnum"; domain = []; range = bv_s; interp = Some op_num_bv; int_params = [v] }
let bv3 : expr = c0 (bv_d 3)
let bv5 : expr = c0 (bv_d 5)

(* `(= bv3 bv5) = (= bv5 bv3)`, `eq_symm` over `op_eq` applied to two
   literal bit-vector numerals -- demonstrates `provably_distinct`'s
   `is_bv_num_const` disjunct is a genuine, exercised fact (not just a
   decidable definition that happens to typecheck): `bv3 <> bv5`
   witnesses `3 <> 5 (mod 2^32)` post-`bv32_value` reduction. *)
let eq_bv_d : func_decl = { decl_name = "="; domain = [bv_s; bv_s]; range = bool_s; interp = Some op_eq; int_params = [] }
let lit_bv_s : expr = c2 eq_bv_d bv3 bv5
let lit_bv_t : expr = c2 eq_bv_d bv5 bv3
let lit_bv_leaf : proof = mk_rewrite_leaf lit_bv_s lit_bv_t

let lemma_lit_bv_distinct ()
  : Lemma (provably_distinct bv3 bv5)
  = ()

let lemma_lit_bv_leaf_matched ()
  : Lemma (all_matched lit_bv_leaf)
  = ()

let lemma_lit_bv_leaf_true (rho:env value)
  : Lemma (eval the_interpretation lit_bv_s rho == eval the_interpretation lit_bv_t rho)
  = lemma_lit_bv_leaf_matched ();
    lemma_matched_proof_true lit_bv_leaf rho


