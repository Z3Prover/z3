module Z3IndependentDefinitionSkolem

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module SK = Z3SkolemSyntax
module E = Z3SortedSkolem
module DS = Z3SortedDependentSkolem
module Q = Z3SortedQuantifier
module P = Z3DocumentSyntax
module SP = Z3SortedProof
module Context = Z3IndependentDefinitionContext
module TR = Z3TypedRoot

let rec closed_fresh (s:S.checked_schema) (ds:list (E.definition s)) (es:list expr)
  : Tot bool (decreases ds) =
  match ds with
  | [] -> true
  | d :: rest -> SK.fresh_args d.SK.witnesses es && closed_fresh s rest es

let rec dependent_fresh (s:S.checked_schema) (ds:list (DS.definition s)) (es:list expr)
  : Tot bool (decreases ds) =
  match ds with
  | [] -> true
  | d :: rest -> SK.fresh_args d.SK.witnesses es && dependent_fresh s rest es

val lemma_closed_truths (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (ds:list (E.definition s)) (other:V.interpretation base (S.signature s)) (es:list expr)
  : Lemma (requires closed_fresh s ds es)
    (ensures T.truths s bc eq (E.build s bc eq choice ds other) es ==
             T.truths s bc eq other es)

val lemma_dependent_truths (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (ds:list (DS.definition s)) (other:V.interpretation base (S.signature s)) (es:list expr)
  : Lemma (requires dependent_fresh s ds es)
    (ensures T.truths s bc eq (DS.build s bc eq choice ds other) es ==
             T.truths s bc eq other es)

let compatible (s:S.checked_schema) (doc:P.document)
  (items:list (Context.item s doc.P.assertions)) : bool =
  let closed = SP.epsilon_context s doc in
  let dependent = SP.dependent_context s doc closed in
  let formulas = Context.formulas s doc.P.assertions items in
  closed_fresh s closed formulas && dependent_fresh s dependent formulas

val build (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (items:list (Context.item s doc.P.assertions))
  (other:V.interpretation base (S.signature s))
  : GTot (V.interpretation base (S.signature s))

val lemma_build_expansion (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (items:list (Context.item s doc.P.assertions))
  (other:V.interpretation base (S.signature s))
  : Lemma (build s bc eq choice doc items other ==
    SP.full_extension s bc eq choice doc (Context.build s bc eq doc.P.assertions items other))

val lemma_build (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (items:list (Context.item s doc.P.assertions))
  (other:V.interpretation base (S.signature s))
  : Lemma (requires Context.ordered s doc.P.assertions items /\ compatible s doc items /\
                    Q.forall_model s bc other /\ E.exists_model s bc other)
    (ensures (
      let extended = build s bc eq choice doc items other in
      T.truths s bc eq extended (Context.formulas s doc.P.assertions items) /\
      T.truths s bc eq extended doc.P.assertions == T.truths s bc eq other doc.P.assertions /\
      T.truths s bc eq extended
        (SP.epsilon_equations s (SP.epsilon_context s doc) doc.P.entries) /\
      T.truths s bc eq extended
        (DS.closures s (SP.dependent_context s doc (SP.epsilon_context s doc))) /\
      Q.forall_model s bc extended /\ E.exists_model s bc extended))

val lemma_build_root (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (choice:E.hilbert_choice (TR.carrier u) s) (doc:P.document)
  (items:list (Context.item s doc.P.assertions)) (other:TR.interp u s)
  : Lemma (requires TR.root_model u s other)
    (ensures TR.root_model u s (build s bc eq choice doc items other))
