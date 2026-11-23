module Z3IndependentDefinitionRoot

open Z3AstTheory
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module TR = Z3TypedRoot
module Root = Z3SortedRootDocument
module Model = Z3IndependentDefinitionModel
module Context = Z3IndependentDefinitionContext
module L = FStar.List.Tot

let lemma_recognizer (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (inputs:list expr) (d:Context.item s inputs) (other:TR.interp u s) (f:func_decl)
  : Lemma (requires TR.recognizer_at u s other f)
    (ensures TR.recognizer_at u s
      (Model.override s bc eq other inputs d.formula d.definition) f) =
  if f = d.definition.D.symbol then ()
  else match S.find_recognizer f s.S.cases with
  | None -> ()
  | Some c ->
    introduce forall (v:TR.tvalue u s c.S.constructor.range).
      TR.recognizer_case u s
        (Model.override s bc eq other inputs d.formula d.definition) f c v
    with Model.lemma_override_application s bc eq other inputs d.formula d.definition f [v]

let lemma_accessor (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (inputs:list expr) (d:Context.item s inputs) (other:TR.interp u s) (f:func_decl)
  : Lemma (requires TR.accessor_at u s other f)
    (ensures TR.accessor_at u s
      (Model.override s bc eq other inputs d.formula d.definition) f) =
  if f = d.definition.D.symbol then ()
  else match S.find_accessor f s.S.cases with
  | None -> ()
  | Some r ->
    introduce forall (ys:TR.targuments u s r.S.matched_case.S.constructor.domain).
      TR.accessor_case u s
        (Model.override s bc eq other inputs d.formula d.definition) f r ys
    with (
      assert (f.domain == [r.S.matched_case.S.constructor.range]);
      let v = S.constructor_value s r.S.matched_case ys in
      assert_norm (V.fields_have_sorts (S.signature s) [r.S.matched_case.S.constructor.range] [v] ==
                   V.has_sort (S.signature s) r.S.matched_case.S.constructor.range v);
      Model.lemma_override_application s bc eq other inputs d.formula d.definition f [v])

let lemma_override_root (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (inputs:list expr) (d:Context.item s inputs) (other:TR.interp u s)
  : Lemma (requires TR.root_model u s other)
    (ensures TR.root_model u s
      (Model.override s bc eq other inputs d.formula d.definition)) =
  let j = Model.override s bc eq other inputs d.formula d.definition in
  Model.lemma_override_quantification s bc eq other inputs d.formula d.definition;
  introduce forall (bound:list sort) (body:TR.body_of u s bound bool_sort).
    TR.forall_case u s j bound body
  with assert (TR.forall_case u s other bound body);
  introduce forall (bound:list sort) (body:TR.body_of u s bound bool_sort).
    TR.exists_case u s j bound body
  with assert (TR.exists_case u s other bound body);
  introduce forall (f:func_decl) (xs:TR.targuments u s f.domain).
    (not (TR.datatype_kind f) /\ Some? (TR.interpreted u s f xs)) ==>
    j.V.application f xs == Some?.v (TR.interpreted u s f xs)
  with (
    if f = d.definition.D.symbol then Root.lemma_free_declaration (S.signature s) f
    else Model.lemma_override_application s bc eq other inputs d.formula d.definition f xs);
  introduce forall (f:func_decl{L.mem f (S.signature s)}) (xs:TR.targuments u s f.domain).
    j.V.application f xs == V.construct (S.signature s) f xs
  with (
    if f <> d.definition.D.symbol then
      Model.lemma_override_application s bc eq other inputs d.formula d.definition f xs);
  introduce forall (f:func_decl). TR.recognizer_at u s j f
  with (assert (TR.recognizer_at u s other f); lemma_recognizer u s bc eq inputs d other f);
  introduce forall (f:func_decl). TR.accessor_at u s j f
  with (assert (TR.accessor_at u s other f); lemma_accessor u s bc eq inputs d other f)

let rec lemma_build_root (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (inputs:list expr) (items:list (Context.item s inputs)) (other:TR.interp u s)
  : Lemma (requires TR.root_model u s other)
    (ensures TR.root_model u s (Context.build s bc eq inputs items other))
    (decreases items) =
  match items with
  | [] -> Context.lemma_build_nil s bc eq inputs other
  | d :: rest ->
    lemma_build_root u s bc eq inputs rest other;
    Context.lemma_build_cons s bc eq inputs d rest other;
    lemma_override_root u s bc eq inputs d (Context.build s bc eq inputs rest other)
