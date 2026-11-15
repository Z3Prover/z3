module Z3IndependentGroundDefinitionRoot

open Z3AstTheory
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module TR = Z3TypedRoot
module Root = Z3SortedRootDocument
module Ground = Z3IndependentGroundDefinition
module A = Z3SortedArray
module L = FStar.List.Tot

let lemma_recognizer (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (inputs:list expr) (formula:expr) (d:Ground.definition s inputs formula)
  (other:TR.interp u s) (f:func_decl)
  : Lemma (requires TR.recognizer_at u s other f)
    (ensures TR.recognizer_at u s (Ground.override s bc eq other inputs formula d) f) =
  if f = d.D.symbol then ()
  else match S.find_recognizer f s.S.cases with
  | None -> ()
  | Some c ->
    introduce forall (v:TR.tvalue u s c.S.constructor.range).
      TR.recognizer_case u s (Ground.override s bc eq other inputs formula d) f c v
    with Ground.lemma_override_application s bc eq other inputs formula d f [v]

let lemma_accessor (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (inputs:list expr) (formula:expr) (d:Ground.definition s inputs formula)
  (other:TR.interp u s) (f:func_decl)
  : Lemma (requires TR.accessor_at u s other f)
    (ensures TR.accessor_at u s (Ground.override s bc eq other inputs formula d) f) =
  if f = d.D.symbol then ()
  else match S.find_accessor f s.S.cases with
  | None -> ()
  | Some r ->
    introduce forall (ys:TR.targuments u s r.S.matched_case.S.constructor.domain).
      TR.accessor_case u s (Ground.override s bc eq other inputs formula d) f r ys
    with (
      assert (f.domain == [r.S.matched_case.S.constructor.range]);
      let v = S.constructor_value s r.S.matched_case ys in
      assert_norm (V.fields_have_sorts (S.signature s) [r.S.matched_case.S.constructor.range] [v] ==
                   V.has_sort (S.signature s) r.S.matched_case.S.constructor.range v);
      Ground.lemma_override_application s bc eq other inputs formula d f [v])

let lemma_override_root (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (inputs:list expr) (formula:expr) (d:Ground.definition s inputs formula)
  (other:TR.interp u s)
  : Lemma (requires TR.root_model u s other)
    (ensures TR.root_model u s (Ground.override s bc eq other inputs formula d)) =
  let j = Ground.override s bc eq other inputs formula d in
  Ground.lemma_override_quantification s bc eq other inputs formula d;
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
    if f = d.D.symbol then Root.lemma_free_declaration (S.signature s) f
    else Ground.lemma_override_application s bc eq other inputs formula d f xs);
  introduce forall (f:func_decl{L.mem f (S.signature s)}) (xs:TR.targuments u s f.domain).
    j.V.application f xs == V.construct (S.signature s) f xs
  with (
    if f <> d.D.symbol then Ground.lemma_override_application s bc eq other inputs formula d f xs);
  introduce forall (f:func_decl). TR.recognizer_at u s j f
  with (assert (TR.recognizer_at u s other f); lemma_recognizer u s bc eq inputs formula d other f);
  introduce forall (f:func_decl). TR.accessor_at u s j f
  with (assert (TR.accessor_at u s other f); lemma_accessor u s bc eq inputs formula d other f)

let lemma_override_array_model (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (inputs:list expr) (formula:expr) (d:Ground.definition s inputs formula)
  (other:TR.interp u s) (family:A.family (TR.carrier u) (S.signature s))
  : Lemma (requires A.model s bc eq other family)
    (ensures A.model s bc eq (Ground.override s bc eq other inputs formula d) family) =
  let j = Ground.override s bc eq other inputs formula d in
  introduce forall (index:sort) (element:sort{family.supports index element})
                   (a:A.array_value (TR.carrier u) (S.signature s) index element)
                   (k:V.value (TR.carrier u) (S.signature s) index).
    T.application s bc eq j (A.select_decl index element) [a; k] ==
    (family.arrays index element).read a k
  with Ground.lemma_override_application s bc eq other inputs formula d
    (A.select_decl index element) [a; k];
  introduce forall (index:sort) (element:sort{family.supports index element})
                   (a:A.array_value (TR.carrier u) (S.signature s) index element)
                   (k:V.value (TR.carrier u) (S.signature s) index)
                   (v:V.value (TR.carrier u) (S.signature s) element).
    T.application s bc eq j (A.store_decl index element) [a; k; v] ==
    (family.arrays index element).write a k v
  with Ground.lemma_override_application s bc eq other inputs formula d
    (A.store_decl index element) [a; k; v];
  introduce forall (index:sort) (element:sort{family.supports index element})
                   (a b:A.array_value (TR.carrier u) (S.signature s) index element).
    T.application s bc eq j (A.ext_decl index element) [a; b] ==
    (family.arrays index element).difference a b
  with Ground.lemma_override_application s bc eq other inputs formula d
    (A.ext_decl index element) [a; b]
