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
