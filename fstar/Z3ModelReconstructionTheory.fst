module Z3ModelReconstructionTheory

(*
   F* formalization of the core soundness property of
   `src/ast/simplifiers/model_reconstruction_trail.cpp`, the
   cross-cutting mechanism every `ast/simplifiers` preprocessor relies
   on to reconstruct a model of the *original* (pre-simplification)
   formula set from a model of the *simplified* one.

   Correspondence with the `.cpp`:

     `model_reconstruction_trail` ~ a stack of `trail` entries, each
     produced when a simplifier eliminates a symbol (or sub-formula)
     from the problem: `replace_vars_trail`/`updt_trail` register a
     substitution for an eliminated symbol `f` by its definition
     (`add(f, def, dep)`, see `add_vars`/`append`), `hide_trail`
     registers that `f` should not be reported in the final model, and
     the "loose" variants (`is_loose_subst`/`is_loose_constraint`)
     re-insert a removed formula instead of extending the model when
     its free variables are still relevant.

     `replay` ~ walks the trail newest-to-oldest, and for every `def`
     entry extends the *model being built* by assigning the eliminated
     symbol's interpretation from its definition, evaluated in the
     model built so far -- i.e. exactly the `update_interp`/
     `macro_interp` construction below, iterated.

   Scope decision for this first pass: `model_reconstruction_trail.cpp`
   supports eliminating function symbols of arbitrary arity
   (`is_def()`, via `macro_replacer`, substituting `f(x1..xn)` by a
   body with xi's as formal parameters) as well as plain ground
   substitutions (`is_subst()`, via `expr_replacer`, substituting one
   *closed* sub-term by another -- the case already modeled by
   `Z3SimplifierTheory.subst`/`lemma_subst_cong`). This first pass
   formalizes the arity-0 case precisely (`f` an eliminated constant,
   `def` a closed definition) -- the case `propagate_values.cpp`,
   `solve_eqs.cpp`, `solve_context_eqs.cpp` and `extract_eqs.cpp`
   actually produce (a shared constant/atom found equal to a closed
   value) -- and states it as the new, model-reconstruction-specific
   fact this file adds beyond `lemma_subst_cong`: rather than fixing an
   interpretation and relating two *terms* under it (what
   `lemma_subst_cong` does), model reconstruction fixes a *term
   rewrite* (the elimination that already happened) and relates two
   *interpretations* -- the one found for the simplified problem, and
   its canonical extension for the original one -- showing the
   extension is forced to agree with syntactic substitution. General
   positive-arity macro definitions (`is_def()` with arity > 0,
   requiring De Bruijn index shifting of `def` under nested binders
   when inlined) and the "loose" re-insertion branches (a scheduling
   decision about *which* removed formulas must be re-examined, not a
   soundness-relevant rewrite) are deferred, see
   `MODEL_RECONSTRUCTION_REPORT.md`.
*)

open Z3AstTheory
open Z3SimplifierTheory

(* ----------------------------------------------------------------- *)
(* Interpretation extension                                            *)
(* ----------------------------------------------------------------- *)

/// `update_interp i f g` is the interpretation agreeing with `i` on
/// every symbol except the uninterpreted `f`, whose interpretation is
/// replaced by `g` -- the semantic counterpart of
/// `generic_model_converter::add(f, def)` installing a new entry for
/// `f` in the model being reconstructed (`model_reconstruction_trail.cpp`'s
/// `get_model_converter`/`append`, and ultimately
/// `generic_model_converter::convert`'s per-symbol model update).
let update_interp (#value:Type) (i:interpretation value)
    (f:func_decl{is_uninterp_decl f}) (g:list value -> value)
  : interpretation value =
  { i with uninterp_app = (fun f' args -> if f' = f then g args else i.uninterp_app f' args) }

/// `f`'s own node (an arity-0 uninterpreted constant, i.e. `App f
/// []`) evaluates to exactly `g []` under `update_interp i f g`,
/// regardless of what `i` said about `f` -- the basic "write, then
/// read back" fact about the update.
let lemma_update_interp_same (#value:Type) (i:interpretation value)
    (f:func_decl{is_uninterp_decl f}) (g:list value -> value) (rho:env value)
  : Lemma (eval (update_interp i f g) (App f []) rho == g [])
  = ()

/// Any symbol other than `f` keeps its old interpretation under
/// `update_interp i f g` -- the "update does not disturb other
/// entries" fact, needed below to push the update through the
/// structural cases of `eval` that do not touch `f`.
let lemma_update_interp_other (#value:Type) (i:interpretation value)
    (f:func_decl{is_uninterp_decl f}) (g:list value -> value)
    (f':func_decl{is_uninterp_decl f'}) (args:list value)
  : Lemma (requires f' <> f)
          (ensures (update_interp i f g).uninterp_app f' args == i.uninterp_app f' args)
  = ()

(* ----------------------------------------------------------------- *)
(* The model-reconstruction theorem (arity-0 case)                     *)
(* ----------------------------------------------------------------- *)

/// A term matching an arity-0 domain against `sorts_match` must
/// itself have no arguments -- unfolds `sorts_match`'s definition on
/// a concrete `args` shape (an explicit case split, since F*'s SMT
/// encoding does not unfold a recursive boolean function's equations
/// on its own). Used below to turn `wf (App f args)` together with
/// `f.domain = []` into `args == []`.
let lemma_sorts_match_nil (args:list expr)
  : Lemma (requires sorts_match args [] == true) (ensures args == [])
  = match args with
    | [] -> ()
    | _ :: _ -> ()

/// `macro_interp i0 def rho` is the interpretation `f` is given by a
/// `def` entry: `f`'s (unique, arity-0) value is `def` evaluated under
/// the model built so far (`i0`). Since `def` is required closed
/// (`closed def`), the particular environment `eval` is run under is
/// irrelevant (`lemma_closed_eval_env_irrelevant`), so `rho` is an
/// arbitrary ambient environment supplied by the caller purely to
/// have *some* `env value` to evaluate under -- `value` is otherwise
/// left fully abstract, so no environment can be conjured up without
/// one. This mirrors that `model_converter` entries are closed,
/// ground replacement terms (`def` comes from `ast_manager`'s
/// top-level `expr*`, with no free/dangling de Bruijn indices), so in
/// practice the choice of `rho` never matters (see
/// `lemma_macro_interp_env_irrelevant` below).
let macro_interp (#value:Type) (i0:interpretation value) (def:expr) (rho:env value) : (list value -> value) =
  fun (_:list value) -> eval i0 def rho

/// `macro_interp`'s value does not actually depend on the ambient
/// `rho` it was handed, precisely because `def` is closed -- a sanity
/// check that the `rho` parameter above is a harmless technicality,
/// not a hidden extra hypothesis the theorem below secretly needs.
let lemma_macro_interp_env_irrelevant (#value:Type) (i0:interpretation value)
    (def:expr) (rho1 rho2:env value)
  : Lemma (requires quant_extensional i0 /\ closed def)
          (ensures macro_interp i0 def rho1 [] == macro_interp i0 def rho2 [])
  = lemma_closed_eval_env_irrelevant i0 def 0 rho1 rho2

/// The model-reconstruction theorem for an eliminated constant: let
/// `f` be an uninterpreted constant (`is_uninterp_decl f`, `f.domain
/// = []`) and `def` a *closed* definition for it. Build `i1` from
/// `i0` by `macro_interp` (`f`'s slot now holds `def`'s value under
/// `i0`, exactly `generic_model_converter::convert`'s per-entry model
/// update). Then, for *any* host expression `e`, evaluating `e` under
/// the extended model `i1` agrees with evaluating `e` with every
/// occurrence of `f` syntactically replaced by `def` (`subst e (App f
/// []) def`), evaluated under the un-extended `i0`.
///
/// This is the soundness argument the `.cpp`'s trail replay silently
/// relies on: the simplifier eliminated `f` from the problem by
/// rewriting every formula `e` mentioning it to `subst e (App f [])
/// def` (that rewritten formula is what later simplification passes,
/// and finally the solver, actually see); `i0` is a model *of the
/// rewritten problem*. This theorem shows the canonical extension
/// `i1` of `i0` -- the one the trail's replay step constructs -- is a
/// model of `e` itself, i.e. of the *original*, pre-elimination
/// formula, for every `e` whose rewritten form `i0` already
/// satisfies. Composing this lemma along the whole trail (oldest
/// elimination applied first, extending the model one symbol at a
/// time, exactly as `replay` iterates) reconstructs a model of the
/// fully original, pre-simplification problem from a model of the
/// final simplified one.
(* `rho0` and `rho` are deliberately two separate environment
   parameters: `rho0` is only ever used to seed `macro_interp` (i.e.
   to evaluate the *closed* `def`), so its choice is semantically
   irrelevant and it is held fixed throughout the recursion below
   (`i1` is built from `rho0` once, and is the same syntactic
   interpretation at every recursive call); `rho` is the environment
   `e` itself is evaluated under, which does change -- shifted by
   `vs` -- when recursing under a `Quantifier`. Conflating the two
   (reusing `rho`'s shifted copy to also rebuild `i1`) would make
   `i1` a *different* interpretation at each recursion depth, which
   `eval`'s plain (non-extensional) function type cannot be shown
   equal to the outer `i1` without an extra functional-extensionality
   argument; keeping `rho0` fixed sidesteps that entirely. *)
let rec lemma_model_reconstruction
    (#value:Type) (i0:interpretation value)
    (f:func_decl{is_uninterp_decl f /\ f.domain = []}) (def:expr) (rho0:env value)
    (e:expr) (rho:env value)
  : Lemma (requires quant_extensional i0 /\ closed def /\ wf e)
          (ensures eval (update_interp i0 f (macro_interp i0 def rho0)) e rho
                   == eval i0 (subst e (App f []) def) rho)
  = let i1 = update_interp i0 f (macro_interp i0 def rho0) in
    if e = App f [] then begin
      lemma_update_interp_same i0 f (macro_interp i0 def rho0) rho;
      lemma_closed_eval_env_irrelevant i0 def 0 rho0 rho
      (* `eval i1 (App f []) rho == macro_interp i0 def rho0 [] ==
         eval i0 def rho0 == eval i0 def rho` (the last step by
         `def`'s closedness, since `rho0` and `rho` need not agree
         anywhere -- the `forall j<0` hypothesis of
         `lemma_closed_eval_env_irrelevant` is vacuous), and `subst
         (App f []) (App f []) def == def` by `subst`'s `e = old_`
         branch firing, so both sides of the goal reduce to
         `eval i0 def rho`. *)
    end else
      match e with
      | Var _ _ -> ()
      | App f' args ->
        if f' = f then begin
          (* `f` has arity 0, and `e = App f' args` is well-formed, so
             `wf e` gives `sorts_match args f'.domain`; with `f' = f`
             and `f.domain = []` this forces `args = []`
             (`lemma_sorts_match_nil`), i.e. `e = App f []`,
             contradicting that this `else` branch is only reached
             when `e <> App f []`. This branch is therefore
             unreachable; deriving the contradiction explicitly (via
             `False`'s elimination) is what lets a plain `()` close an
             arbitrary goal here. *)
          lemma_sorts_match_nil args
        end else
          lemma_model_reconstruction_args i0 f def rho0 args rho
      | Quantifier qk bound_sorts body ->
        let n = List.Tot.length bound_sorts in
        let aux (vs:list value{List.Tot.length vs = n})
          : Lemma (eval i1 body (shift vs rho) == eval i0 (subst body (App f []) def) (shift vs rho))
          = lemma_model_reconstruction i0 f def rho0 body (shift vs rho)
        in
        FStar.Classical.forall_intro aux

and lemma_model_reconstruction_args
    (#value:Type) (i0:interpretation value)
    (f:func_decl{is_uninterp_decl f /\ f.domain = []}) (def:expr) (rho0:env value)
    (args:list expr) (rho:env value)
  : Lemma (requires quant_extensional i0 /\ closed def /\ wf_args args)
          (ensures eval_args (update_interp i0 f (macro_interp i0 def rho0)) args rho
                   == eval_args i0 (subst_args args (App f []) def) rho)
  = match args with
    | [] -> ()
    | a :: args' ->
      lemma_model_reconstruction i0 f def rho0 a rho;
      lemma_model_reconstruction_args i0 f def rho0 args' rho

(* ----------------------------------------------------------------- *)
(* The model-reconstruction theorem, arity-n follow-up                 *)
(* ----------------------------------------------------------------- *)

(* The restriction to arity-0 `f` above is the case
   `propagate_values.cpp`/`solve_eqs.cpp`/`solve_context_eqs.cpp`/
   `extract_eqs.cpp` produce, but not `reduce_args_simplifier.cpp`'s
   `mk_mc`, which pushes a `def` entry for a function symbol `f` of
   its *original* arity, defined by a chain of `ite`s over equality
   tests against recorded argument values (see `reduce_args_simplifier.cpp`'s
   module comment and `mk_mc`). This section generalizes
   `lemma_model_reconstruction` to arity `n >= 0`, scoped (to stay
   tractable without a full capture-avoiding-substitution-under-binders
   development) to:

     (a) `def` itself contains no quantifier (`no_quantifier def`) --
         true of every `def` `model_reconstruction_trail.cpp`'s actual
         callers build: `reduce_args_simplifier.cpp`'s ite-chains over
         equalities, and `propagate_values.cpp`-style plain substituted
         values, are quantifier-free terms; and

     (b) every *occurrence* of `f` within the host expression `e` is
         applied to arguments that are themselves closed/ground
         (`only_closed_f_args`, below) -- i.e. `f` may occur anywhere
         in `e`, including under `e`'s own quantifiers, but not with
         arguments that depend on those quantifiers' bound variables.

   Under (a), substituting `f`'s `n` formal parameters by argument
   expressions needs no De Bruijn shifting at all: `def` has no
   binders of its own to cross, so a flat, depth-0 list-indexed
   substitution (`inst`/`inst_list` below) suffices; under (b), the
   substituted-in argument expressions are themselves closed, so (by
   the same "a closed term's meaning does not depend on which binders
   enclose the position it is inserted at" principle used throughout
   this file and `Z3SimplifierTheory.fst`) inserting them verbatim
   under `e`'s own binders remains sound without any shifting there
   either. The genuinely harder case this leaves open --
   quantifier-crossing occurrences of `f` whose arguments mention the
   enclosing quantifier's own bound variables (e.g. `forall x. f(x,
   g(x))`) -- is deferred, see `MODEL_RECONSTRUCTION_REPORT.md`. *)

/// `e` contains no `Quantifier` node anywhere.
let rec no_quantifier (e:expr) : bool =
  match e with
  | Var _ _ -> true
  | App _ args -> no_quantifier_args args
  | Quantifier _ _ _ -> false
and no_quantifier_args (args:list expr) : bool =
  match args with
  | [] -> true
  | a :: args' -> no_quantifier a && no_quantifier_args args'

/// Flat (depth-0) simultaneous substitution of `def`'s formal
/// parameters `Var 0, ..., Var (n-1)` by the expressions `subs` (`n =
/// List.length subs`), used only when `no_quantifier def` holds (so
/// there is never a binder inside `def` to cross, hence no de Bruijn
/// shifting concern); the `Quantifier` case is dead code under that
/// hypothesis (see `lemma_inst_eval`'s proof) and simply returns `def`
/// unchanged to keep `inst` total.
let rec inst (subs:list expr) (def:expr) : expr =
  match def with
  | Var idx _ -> if idx < List.Tot.length subs then List.Tot.index subs idx else def
  | App f' args -> App f' (inst_list subs args)
  | Quantifier _ _ _ -> def
and inst_list (subs:list expr) (args:list expr) : list expr =
  match args with
  | [] -> []
  | a :: args' -> inst subs a :: inst_list subs args'

/// `eval_args` does not change a list's length -- needed so that
/// `List.Tot.index (eval_args i subs rho) idx` typechecks at the same
/// `idx < List.Tot.length subs` bound used for `subs` itself.
let rec lemma_eval_args_length (#value:Type) (i:interpretation value) (subs:list expr) (rho:env value)
  : Lemma (ensures List.Tot.length (eval_args i subs rho) == List.Tot.length subs)
  = match subs with
    | [] -> ()
    | _ :: subs' -> lemma_eval_args_length i subs' rho

/// A list `eval`'d element-by-element agrees with evaluating the
/// corresponding source expression at the same index -- a routine
/// `List.Tot.index`/`eval_args` commutation fact, needed to relate
/// `inst`'s `Var idx` case (which looks up `subs` syntactically) to
/// `shift`'s `vs` lookup (which looks up the already-`eval`'d values).
let rec lemma_eval_args_index (#value:Type) (i:interpretation value) (subs:list expr) (idx:nat{idx < List.Tot.length subs}) (rho:env value)
  : Lemma (ensures List.Tot.length (eval_args i subs rho) == List.Tot.length subs /\
                    List.Tot.index (eval_args i subs rho) idx == eval i (List.Tot.index subs idx) rho)
  = lemma_eval_args_length i subs rho;
    match subs with
    | a :: subs' -> if idx = 0 then () else lemma_eval_args_index i subs' (idx - 1) rho

/// The substitution-evaluation commutation theorem for `inst`: under
/// `no_quantifier def` and `closed_at (List.length subs) def` (`def`'s
/// only free references are its `n` formal parameters) and
/// `closed_at_args 0 subs` (every substituted-in expression is
/// closed/ground), evaluating `inst subs def` agrees with evaluating
/// `def` directly in an environment where the formal parameters are
/// bound to `subs`'s (already-`eval`'d) values -- exactly `shift
/// (eval_args i subs rho) rho`, reusing `Z3AstTheory.shift` precisely
/// because `inst`, under `no_quantifier def`, never needs to track any
/// depth beyond 0.
let rec lemma_inst_eval (#value:Type) (i:interpretation value) (subs:list expr) (def:expr) (rho:env value)
  : Lemma (requires quant_extensional i /\ no_quantifier def /\
                     closed_at (List.Tot.length subs) def /\ closed_at_args 0 subs)
          (ensures eval i (inst subs def) rho == eval i def (shift (eval_args i subs rho) rho))
  = match def with
    | Var idx _ ->
      if idx < List.Tot.length subs then lemma_eval_args_index i subs idx rho
      (* else: `closed_at (List.Tot.length subs) (Var idx _)` is
         `idx < List.Tot.length subs`, contradicting `idx >=
         List.Tot.length subs`; this branch is unreachable. *)
    | App f' args -> lemma_inst_eval_defargs i subs args rho
    (* `Quantifier _ _ _`: `no_quantifier def` is `false` here by
       `no_quantifier`'s own definition, contradicting the hypothesis;
       unreachable. *)

and lemma_inst_eval_defargs (#value:Type) (i:interpretation value) (subs:list expr) (args:list expr) (rho:env value)
  : Lemma (requires quant_extensional i /\ no_quantifier_args args /\
                     closed_at_args (List.Tot.length subs) args /\ closed_at_args 0 subs)
          (ensures eval_args i (inst_list subs args) rho == eval_args i args (shift (eval_args i subs rho) rho))
  = match args with
    | [] -> ()
    | a :: args' ->
      lemma_inst_eval i subs a rho;
      lemma_inst_eval_defargs i subs args' rho

/// Indexing into a list every element of which is closed yields a
/// closed element -- an `index`/`closed_at_args` commutation fact
/// analogous to `lemma_eval_args_index`, needed for `inst`'s `Var idx`
/// case (which looks up `subs` syntactically by index).
let rec lemma_closed_at_args_index (d:nat) (args:list expr) (idx:nat{idx < List.Tot.length args})
  : Lemma (requires closed_at_args d args)
          (ensures closed_at d (List.Tot.index args idx))
  = match args with
    | a :: args' -> if idx = 0 then () else lemma_closed_at_args_index d args' (idx - 1)

/// Syntactic counterpart of `lemma_inst_eval`: substituting closed
/// expressions into a quantifier-free, arity-matched `def` yields a
/// closed result -- needed to re-apply `lemma_inst_eval` at nested
/// (already macro-expanded) occurrences of `f` below.
let rec lemma_inst_closed (subs:list expr) (def:expr)
  : Lemma (requires no_quantifier def /\
                     closed_at (List.Tot.length subs) def /\ closed_at_args 0 subs)
          (ensures closed_at 0 (inst subs def))
  = match def with
    | Var idx _ -> if idx < List.Tot.length subs then lemma_closed_at_args_index 0 subs idx
    | App f' args -> lemma_inst_closed_defargs subs args
    | Quantifier _ _ _ -> ()

and lemma_inst_closed_defargs (subs:list expr) (args:list expr)
  : Lemma (requires no_quantifier_args args /\
                     closed_at_args (List.Tot.length subs) args /\ closed_at_args 0 subs)
          (ensures closed_at_args 0 (inst_list subs args))
  = match args with
    | [] -> ()
    | a :: args' -> lemma_inst_closed subs a; lemma_inst_closed_defargs subs args'

/// Every occurrence of `f` within `e` (at any nesting depth, including
/// under `e`'s own quantifiers) is applied to closed/ground arguments
/// -- the precise well-formedness condition under which this section's
/// theorem applies (see the scope discussion above).
let rec only_closed_f_args (f:func_decl) (e:expr) : prop =
  match e with
  | Var _ _ -> True
  | App f' args -> (f' = f ==> closed_at_args 0 args) /\ only_closed_f_args_args f args
  | Quantifier _ _ body -> only_closed_f_args f body
and only_closed_f_args_args (f:func_decl) (args:list expr) : prop =
  match args with
  | [] -> True
  | a :: args' -> only_closed_f_args f a /\ only_closed_f_args_args f args'

/// Macro-expansion over a host expression: every occurrence of `f`
/// (its arguments first recursively expanded, bottom-up) is replaced
/// by `def` with its formal parameters instantiated to those
/// (expanded) arguments -- the syntactic counterpart of what
/// `macro_replacer`/`reduce_args_rw_cfg::reduce_app` does at rewrite
/// time.
let rec expand_macro (f:func_decl) (def:expr) (e:expr) : expr =
  match e with
  | Var _ _ -> e
  | App f' args ->
    let args' = expand_macro_args f def args in
    if f' = f then inst args' def else App f' args'
  | Quantifier qk bound_sorts body -> Quantifier qk bound_sorts (expand_macro f def body)
and expand_macro_args (f:func_decl) (def:expr) (args:list expr) : list expr =
  match args with
  | [] -> []
  | a :: args' -> expand_macro f def a :: expand_macro_args f def args'

/// A closed expression remains closed at any larger depth -- the
/// "closed terms don't care how many extra binders enclose them"
/// monotonicity fact, needed below because `inst`'s result is always
/// `closed_at 0` (by `lemma_inst_closed`) regardless of how deeply
/// nested the `f`-occurrence being expanded is inside `e`'s own
/// quantifiers (which only guarantee `closed_at d` for the ambient
/// depth `d`, not `closed_at 0`).
let rec lemma_closed_at_monotone (d1:nat) (d2:nat{d2 >= d1}) (e:expr)
  : Lemma (requires closed_at d1 e) (ensures closed_at d2 e) (decreases e)
  = match e with
    | Var _ _ -> ()
    | App _ args -> lemma_closed_at_monotone_args d1 d2 args
    | Quantifier _ bound_sorts body ->
      lemma_closed_at_monotone (d1 + List.Tot.length bound_sorts) (d2 + List.Tot.length bound_sorts) body
and lemma_closed_at_monotone_args (d1:nat) (d2:nat{d2 >= d1}) (args:list expr)
  : Lemma (requires closed_at_args d1 args) (ensures closed_at_args d2 args) (decreases args)
  = match args with
    | [] -> ()
    | a :: args' -> lemma_closed_at_monotone d1 d2 a; lemma_closed_at_monotone_args d1 d2 args'

/// `sorts_match` forces matching lengths -- needed to transport
/// `wf`'s `sorts_match args f.domain` into `List.Tot.length args =
/// List.Tot.length f.domain`.
let rec lemma_sorts_match_length (args:list expr) (dom:list sort)
  : Lemma (requires sorts_match args dom) (ensures List.Tot.length args == List.Tot.length dom)
  = match args, dom with
    | [], [] -> ()
    | a :: args', d :: dom' -> lemma_sorts_match_length args' dom'
    | _, _ -> ()

/// `expand_macro_args` does not change a list's length -- needed
/// alongside `lemma_sorts_match_length` to meet `lemma_inst_closed`'s
/// arity-matching hypothesis after expansion.
let rec lemma_expand_macro_args_length (f:func_decl) (def:expr) (args:list expr)
  : Lemma (ensures List.Tot.length (expand_macro_args f def args) == List.Tot.length args)
  = match args with
    | [] -> ()
    | a :: args' -> lemma_expand_macro_args_length f def args'

/// `expand_macro` preserves "closed at any depth `d`": expanding `f`'s
/// occurrences (each applied to absolutely closed, `closed_at 0`,
/// arguments, by `only_closed_f_args`, regardless of `e`'s own ambient
/// depth `d`) inside a `closed_at d` host `e` produces another
/// `closed_at d` expression -- needed so that a nested occurrence of
/// `f` (inside another occurrence's arguments, or beneath `e`'s own
/// quantifiers) still meets `lemma_inst_eval`'s `closed_at_args 0
/// subs` hypothesis after its own arguments have been expanded.
let rec lemma_expand_macro_closed (f:func_decl{is_uninterp_decl f}) (def:expr) (d:nat) (e:expr)
  : Lemma (requires no_quantifier def /\ closed_at (List.Tot.length f.domain) def /\
                     closed_at d e /\ only_closed_f_args f e /\ wf e)
          (ensures closed_at d (expand_macro f def e)) (decreases e)
  = match e with
    | Var _ _ -> ()
    | App f' args ->
      lemma_expand_macro_closed_args f def d args;
      if f' = f then begin
        (* `only_closed_f_args`'s own `App` case (this occurrence of
           `f`) gives `closed_at_args 0 args` *absolutely*, regardless
           of the ambient depth `d`; re-derive `expand_macro_args`'s
           closedness at depth `0` specifically from that (distinct
           from the depth-`d` fact already established above) to meet
           `lemma_inst_closed`'s requirement. *)
        lemma_expand_macro_closed_args f def 0 args;
        lemma_sorts_match_length args f'.domain;
        lemma_expand_macro_args_length f def args;
        lemma_inst_closed (expand_macro_args f def args) def;
        lemma_closed_at_monotone 0 d (inst (expand_macro_args f def args) def)
      end
    | Quantifier qk bound_sorts body ->
      lemma_expand_macro_closed f def (d + List.Tot.length bound_sorts) body

and lemma_expand_macro_closed_args (f:func_decl{is_uninterp_decl f}) (def:expr) (d:nat) (args:list expr)
  : Lemma (requires no_quantifier def /\ closed_at (List.Tot.length f.domain) def /\
                     closed_at_args d args /\ only_closed_f_args_args f args /\ wf_args args)
          (ensures closed_at_args d (expand_macro_args f def args)) (decreases args)
  = match args with
    | [] -> ()
    | a :: args' ->
      lemma_expand_macro_closed f def d a;
      lemma_expand_macro_closed_args f def d args'

/// The arity-`n` generalization of `macro_interp`: `f`'s interpretation
/// now genuinely depends on its argument list `vs` (unlike the
/// arity-0 `macro_interp`, which ignores its `list value` argument
/// entirely since it is always `[]`) -- `def` is evaluated with its
/// `n` formal parameters (`Var 0 .. Var (n-1)`) bound to `vs` via
/// `shift`, matching `inst`'s own convention for how `def`'s formal
/// parameters are indexed.
let macro_interp_n (#value:Type) (i0:interpretation value) (def:expr) (rho0:env value) : (list value -> value) =
  fun (vs:list value) -> eval i0 def (shift vs rho0)

/// The arity-`n` model-reconstruction theorem: let `f` be uninterpreted
/// of arity `n = List.length f.domain`, `def` a quantifier-free
/// expression with `closed_at n def` (its only free references are
/// `f`'s `n` formal parameters), `rho0` an arbitrary ambient
/// environment (only ever used to seed the unreachable "beyond `n`"
/// slot of `shift`, exactly as in the arity-0 case), and `e` a closed,
/// well-formed host expression in which every occurrence of `f` is
/// applied to closed/ground arguments (`only_closed_f_args`). Then
/// extending `i0` by assigning `f`'s interpretation from `def`
/// (`update_interp i0 f (macro_interp_n i0 def rho0)`, generalizing
/// `macro_interp` to arity `n` by reusing `shift` on the `n`-element
/// value list) agrees, on `e`, with evaluating `e`'s `f`-eliminated
/// form (`expand_macro f def e`) under the un-extended `i0`:
/// generalizing `lemma_model_reconstruction` from "eliminated
/// constant" to "eliminated function of ground-argument occurrences".
let rec lemma_model_reconstruction_n
    (#value:Type) (i0:interpretation value) (f:func_decl{is_uninterp_decl f}) (def:expr) (rho0:env value)
    (e:expr) (rho:env value)
  : Lemma (requires quant_extensional i0 /\ no_quantifier def /\
                     closed_at (List.Tot.length f.domain) def /\
                     wf e /\ only_closed_f_args f e)
          (ensures eval (update_interp i0 f (macro_interp_n i0 def rho0)) e rho
                   == eval i0 (expand_macro f def e) rho)
  = let i1 = update_interp i0 f (macro_interp_n i0 def rho0) in
    match e with
    | Var _ _ -> ()
    | App f' args ->
      lemma_model_reconstruction_n_args i0 f def rho0 args rho;
      if f' = f then begin
        (* `only_closed_f_args` gives `closed_at_args 0 args`
           *absolutely*, independent of `e`'s own ambient quantifier
           depth, so `expand_macro_closed_args` is invoked at depth
           `0` here (not tied to any surrounding binder depth).
           `wf e` gives `sorts_match args f.domain`, so
           `List.Tot.length args = List.Tot.length f.domain`;
           combined with the args lemma (just invoked) and
           `lemma_expand_macro_closed_args` (to meet
           `lemma_inst_eval`'s `closed_at_args 0 subs`), the two sides
           reduce to the same `eval i0 def (shift ... rho0)` / `eval
           i0 (inst ... def) rho` pair related by `lemma_inst_eval`,
           with `lemma_closed_eval_env_irrelevant` bridging the
           "wrong" `rho0`-seeded tail of the former's `shift` against
           the latter's `rho`-seeded tail (irrelevant since both
           agree exactly on the first `n` slots that `closed_at n
           def` lets `def` actually see). *)
        lemma_sorts_match_length args f'.domain;
        lemma_expand_macro_args_length f def args;
        lemma_expand_macro_closed_args f def 0 args;
        let subs = expand_macro_args f def args in
        let n = List.Tot.length f.domain in
        let vs = eval_args i0 subs rho in
        lemma_eval_args_length i0 subs rho;
        lemma_inst_eval i0 subs def rho;
        lemma_closed_eval_env_irrelevant i0 def n (shift vs rho0) (shift vs rho);
        assert (eval i1 e rho == i1.uninterp_app f (eval_args i1 args rho));
        assert (i1.uninterp_app f (eval_args i1 args rho) == macro_interp_n i0 def rho0 (eval_args i1 args rho));
        assert (eval_args i1 args rho == vs);
        assert (macro_interp_n i0 def rho0 vs == eval i0 def (shift vs rho0));
        assert (eval i0 (expand_macro f def e) rho == eval i0 (inst subs def) rho);
        assert (eval i0 (inst subs def) rho == eval i0 def (shift vs rho))
      end
    | Quantifier qk bound_sorts body ->
      let n = List.Tot.length bound_sorts in
      let aux (vs:list value{List.Tot.length vs = n})
        : Lemma (eval i1 body (shift vs rho) == eval i0 (expand_macro f def body) (shift vs rho))
        = lemma_model_reconstruction_n i0 f def rho0 body (shift vs rho)
      in
      FStar.Classical.forall_intro aux

and lemma_model_reconstruction_n_args
    (#value:Type) (i0:interpretation value) (f:func_decl{is_uninterp_decl f}) (def:expr) (rho0:env value)
    (args:list expr) (rho:env value)
  : Lemma (requires quant_extensional i0 /\ no_quantifier def /\
                     closed_at (List.Tot.length f.domain) def /\
                     wf_args args /\ only_closed_f_args_args f args)
          (ensures eval_args (update_interp i0 f (macro_interp_n i0 def rho0)) args rho
                   == eval_args i0 (expand_macro_args f def args) rho)
  = match args with
    | [] -> ()
    | a :: args' ->
      lemma_model_reconstruction_n i0 f def rho0 a rho;
      lemma_model_reconstruction_n_args i0 f def rho0 args' rho

