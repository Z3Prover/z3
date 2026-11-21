(* A separate judgment for the checked ground fragment of observational
   equality. These constructors preserve observations in the same model,
   which is sufficient for equisatisfiability. General equivalence modulo
   naming requires model-extension/freshness witnesses and is not asserted
   by this theory. Boolean observations compare truth; non-Boolean
   observations require same-sort value agreement as a sufficient witness.
   In particular, ~ remains a separate judgment, not an object-language
   equality. *)
module Z3ObservationalEquality

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module OS = Z3ObservationalSemantics
module Syntax = Z3ObservationalSyntax

let typed_oeq_decl = Syntax.typed_oeq_decl
let oeq_decl = Syntax.oeq_decl
let mk_oeq_expr = Syntax.mk_oeq_expr
let is_oeq = Syntax.is_oeq

let observations_agree (i:interpretation value) (rho:env value) (a b:expr) : prop =
  get_sort a == get_sort b /\
  (if get_sort a = bool_sort then lit_true i rho a <==> lit_true i rho b
   else eval i a rho == eval i b rho)

let boolean_model (i:interpretation value) : prop =
  forall (a:expr) (rho:env value).
    get_sort a == bool_sort ==> VBool? (eval i a rho)

let denotation (#value:Type) (i:interpretation value) (rho:env value)
  : OS.denotation value (fun _ -> true) =
  fun e -> eval i e rho

let lemma_agreement (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (observations_agree i rho a b <==>
           OS.observations_agree (VBool true) (denotation i rho) a b)
  = ()

let lemma_observations_values_typed (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires observations_agree i rho a b /\
                    (get_sort a == bool_sort ==>
                     VBool? (eval i a rho) /\ VBool? (eval i b rho)))
          (ensures eval i a rho == eval i b rho)
  = lemma_agreement i rho a b;
    (if get_sort a = bool_sort then
       match eval i a rho, eval i b rho with VBool _, VBool _ -> () | _, _ -> ());
    OS.lemma_values (VBool true) (VBool false) (denotation i rho) a b

let lemma_observations_values (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires boolean_model i /\ observations_agree i rho a b)
          (ensures eval i a rho == eval i b rho)
  = lemma_observations_values_typed i rho a b

let lemma_mp_oeq_sound (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires observations_agree i rho a b /\ lit_true i rho a)
          (ensures lit_true i rho b)
  = lemma_agreement i rho a b;
    OS.lemma_mp (VBool true) (denotation i rho) a b

let decide_mp_oeq = Syntax.decide_mp_oeq

let lemma_decide_mp_oeq_sound (i:interpretation value) (rho:env value)
                             (a relation:expr)
  : Lemma (requires Some? (decide_mp_oeq a relation) /\ lit_true i rho a /\
                    (match is_oeq relation with
                     | Some (s, t) -> observations_agree i rho s t
                     | None -> False))
          (ensures lit_true i rho (Some?.v (decide_mp_oeq a relation)))
  = (match is_oeq relation with
     | Some (s, t) -> lemma_agreement i rho s t
     | None -> ());
    Syntax.lemma_decide_mp_oeq (VBool true) (denotation i rho) a relation

let lemma_observations_equisatisfiable (i:interpretation value) (a b:expr)
  : Lemma (requires forall (rho:env value). observations_agree i rho a b)
          (ensures (exists (rho:env value). lit_true i rho a) <==>
                   (exists (rho:env value). lit_true i rho b))
  = let aux (rho:env value)
      : Lemma (OS.observations_agree (VBool true) (denotation i rho) a b)
      = lemma_agreement i rho a b in
    FStar.Classical.forall_intro aux;
    OS.lemma_equisatisfiable (VBool true) (denotation i) a b
