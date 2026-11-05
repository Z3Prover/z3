(*
   Z3TypedQuantifier.fst

   The typed quantifier contract shared by the classical model
   (`Z3GhostStandardModel`) and the kernel theorem for quantifier
   instantiation (`Z3QuantifierKernel`).

   * `typed_quantifiers i dom`: `forall`/`exists` over the binder sorts
     `bs` range over exactly the value lists typed by `L.rev bs`
     (`Z3CoreModel.args_typed`, innermost binder first, the de Bruijn order
     of `shift`), and are true exactly when the body holds for all/some of
     them. Value lists of the wrong length or with values outside the
     model's domains are not instances.
   * `quantifier_model i dom`: ONE interpretation and ONE domain assignment
     that satisfy the typed core contracts `Z3CoreModel.core_model`, the
     typed quantifier contract above, and quantifier extensionality
     (`Z3AstTheory.quant_extensional`: a binder's value depends only on the
     values of its body at argument lists of the binder's length).
     `Z3GhostStandardModel.lemma_quantifier_model` proves that the classical
     standard model satisfies all three jointly.

   This is a NEW contract next to `core_model`; `core_model` itself is
   unchanged, and not every core model is a quantifier model (the older
   witness `Z3CoreModel.witness` gives every `forall` the value true).
   Quantifier extensionality is not a lambda law: it says nothing about
   what value a lambda denotes, or about beta reduction.

   The legacy untyped contract `Z3QuantifierInstantiation.
   forall_elimination_model` instead asks a true `forall` to hold at EVERY
   value list of the right length, for instance at a Boolean substituted
   for an integer binder. The classical model does not satisfy it
   (`Z3QuantifierKernelTests.untyped_elimination_fails`); its typed
   counterpart `typed_forall_elimination` follows from `typed_quantifiers`.
*)
module Z3TypedQuantifier

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module CO = Z3CoreModel
module D = Z3Definitions
module DV = Z3DatatypeValue
module L = FStar.List.Tot

let typed_quantifiers (i:interpretation value) (dom:CO.domains) : prop =
  forall (bs:list sort) (s:sort) (body:expr) (rho:env value).
    (eval i (Quantifier Forall_k bs s body) rho == VBool true <==>
     (forall (vs:list value). CO.args_typed dom (L.rev bs) vs ==> eval i body (shift vs rho) == VBool true)) /\
    (eval i (Quantifier Exists_k bs s body) rho == VBool true <==>
     (exists (vs:list value). CO.args_typed dom (L.rev bs) vs /\ eval i body (shift vs rho) == VBool true))

let quantifier_model (i:interpretation value) (dom:CO.domains) : prop =
  CO.core_model i dom /\ typed_quantifiers i dom /\ quant_extensional i

(* --- Typed elimination ----------------------------------------------------- *)

(* A true `forall` holds at every typed value list, and only those are
   claimed. *)
let typed_forall_elimination (i:interpretation value) (dom:CO.domains) : prop =
  forall (bs:list sort) (body:expr) (rho:env value) (vs:list value).
    CO.args_typed dom (L.rev bs) vs /\ lit_true i rho (Quantifier Forall_k bs bool_sort body) ==>
    lit_true i (shift vs rho) body

let lemma_forall_elim (i:interpretation value) (dom:CO.domains) (rho:env value)
                      (bs:list sort) (s:sort) (body:expr) (vs:list value)
  : Lemma (requires typed_quantifiers i dom /\ lit_true i rho (Quantifier Forall_k bs s body) /\
                    CO.args_typed dom (L.rev bs) vs)
          (ensures lit_true i (shift vs rho) body)
  = eliminate forall (bs':list sort) (s':sort) (body':expr) (rho':env value).
      (eval i (Quantifier Forall_k bs' s' body') rho' == VBool true <==>
       (forall (vs':list value). CO.args_typed dom (L.rev bs') vs' ==>
                                eval i body' (shift vs' rho') == VBool true)) /\
      (eval i (Quantifier Exists_k bs' s' body') rho' == VBool true <==>
       (exists (vs':list value). CO.args_typed dom (L.rev bs') vs' /\
                                eval i body' (shift vs' rho') == VBool true))
    with bs s body rho

let lemma_typed_forall_elimination (i:interpretation value) (dom:CO.domains)
  : Lemma (requires typed_quantifiers i dom) (ensures typed_forall_elimination i dom)
  = introduce forall (bs:list sort) (body:expr) (rho:env value) (vs:list value).
      CO.args_typed dom (L.rev bs) vs /\ lit_true i rho (Quantifier Forall_k bs bool_sort body) ==>
      lit_true i (shift vs rho) body
    with FStar.Classical.move_requires (lemma_forall_elim i dom rho bs bool_sort body) vs

(* --- Evaluated arguments are typed by the reversed binder list ------------- *)

let rec lemma_sorts_match_reverse (args acc:list expr) (ss sacc:list sort)
  : Lemma (requires sorts_match args ss /\ sorts_match acc sacc)
          (ensures sorts_match (L.rev_acc args acc) (L.rev_acc ss sacc))
          (decreases args)
  = match args, ss with
    | a :: rest, s :: tail -> lemma_sorts_match_reverse rest (a :: acc) tail (s :: sacc)
    | _, _ -> ()

let rec lemma_scoped_reverse (scope:list sort) (args acc:list expr)
  : Lemma (requires D.scoped_args scope args /\ D.scoped_args scope acc)
          (ensures D.scoped_args scope (L.rev_acc args acc))
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest -> lemma_scoped_reverse scope rest (a :: acc)

(* Arguments scoped in `scope` whose sorts are `bs`, pointwise, evaluate
   under an environment typed for `scope` to a value list typed by
   `L.rev bs` once the argument list is reversed: the list that
   instantiates the binders `bs` (`Var 0` is the last binder). *)
let lemma_reversed_arguments_typed (i:interpretation value) (dom:CO.domains) (scope:list sort)
                                   (args:list expr) (bs:list sort) (rho:env value)
  : Lemma (requires CO.typing i dom /\ D.scoped_args scope args /\ sorts_match args bs /\
                    CO.env_typed dom scope rho)
          (ensures CO.args_typed dom (L.rev bs) (eval_args i (L.rev args) rho))
  = lemma_sorts_match_reverse args [] bs [];
    lemma_scoped_reverse scope args [];
    CO.lemma_typed_args i dom scope (L.rev args) (L.rev bs) rho
