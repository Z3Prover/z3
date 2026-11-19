module Z3SortedRealExtension

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module SK = Z3Skolemization
module E = Z3SortedSkolem
module DS = Z3SortedDependentSkolem
module RL = Z3SortedReal
module L = FStar.List.Tot

(* An uninterpreted declaration (every Skolem witness) is never a classified
   Real operator. *)
let lemma_untagged (f:func_decl)
  : Lemma (requires f.interp == None) (ensures RL.Other? (RL.classify f)) =
  if not (RL.Other? (RL.classify f)) then RL.lemma_classified_tag f

let rec lemma_witness_safe (s:S.checked_schema) (ws:list SK.witness) (f:func_decl)
  : Lemma (requires E.safe_witnesses s ws /\ Some? (SK.component f ws))
          (ensures E.constant_safe s f)
          (decreases ws) =
  match ws with
  | [] -> ()
  | (_, g) :: rest -> if f <> g then lemma_witness_safe s rest f

let lemma_override_agreement (#base:sort -> Type0) (s:S.checked_schema) (d:E.definition s)
                             (vs:V.arguments base (S.signature s) (L.rev d.SK.bound_sorts))
                             (other:V.interpretation base (S.signature s))
  : Lemma (RL.real_agreement s other (E.override s d vs other)) =
  introduce forall (f:func_decl) (xs:V.arguments base (S.signature s) f.domain).
    ~(RL.Other? (RL.classify f)) ==> (E.override s d vs other).V.application f xs == other.V.application f xs
  with (
    if Some? (SK.component f d.SK.witnesses) then (
      lemma_witness_safe s d.SK.witnesses f;
      lemma_untagged f))

let lemma_doverride_agreement (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                              (d:DS.definition s) (other:V.interpretation base (S.signature s))
  : Lemma (RL.real_agreement s other (DS.doverride s bc eq choice d other)) =
  introduce forall (f:func_decl) (xs:V.arguments base (S.signature s) f.domain).
    ~(RL.Other? (RL.classify f)) ==>
      (DS.doverride s bc eq choice d other).V.application f xs == other.V.application f xs
  with (
    if Some? (SK.component f d.SK.witnesses) then (
      DS.lemma_safe_component s d.SK.witnesses f;
      lemma_untagged f))

let rec lemma_build_real (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                         (ds:list (E.definition s)) (other:V.interpretation base (S.signature s))
                         (reals:RL.carrier base)
  : Lemma (requires RL.real_laws s bc eq other reals)
          (ensures RL.real_laws s bc eq (E.build s bc eq choice ds other) reals)
          (decreases ds) =
  match ds with
  | [] -> ()
  | d :: rest ->
    lemma_build_real s bc eq choice rest other reals;
    let older = E.build s bc eq choice rest other in
    lemma_override_agreement s d (E.selected s bc eq choice older d) older;
    RL.lemma_real_laws_transfer s bc eq older (E.build s bc eq choice ds other) reals

let rec lemma_dbuild_real (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                          (ds:list (DS.definition s)) (other:V.interpretation base (S.signature s))
                          (reals:RL.carrier base)
  : Lemma (requires RL.real_laws s bc eq other reals)
          (ensures RL.real_laws s bc eq (DS.build s bc eq choice ds other) reals)
          (decreases ds) =
  match ds with
  | [] -> ()
  | d :: rest ->
    lemma_dbuild_real s bc eq choice rest other reals;
    let older = DS.build s bc eq choice rest other in
    lemma_doverride_agreement s bc eq choice d older;
    RL.lemma_real_laws_transfer s bc eq older (DS.build s bc eq choice ds other) reals
