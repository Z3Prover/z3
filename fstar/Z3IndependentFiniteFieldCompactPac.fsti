module Z3IndependentFiniteFieldCompactPac

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module D = Z3ExprScope
module FF = Z3SortedFiniteField
module IX = Z3ProofIndex
module Core = Z3IndependentFiniteFieldCompactReplay
module Witness = Z3IndependentFiniteFieldWitness
module Monomial = Z3IndependentFiniteFieldMonomial

noeq
type replay = {
  core: Core.state;
  used: IX.index_tree bool;
}

val initial : replay
val step (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:replay) (n:FF.pac_node)
  : Tot (option replay)
val replay_nodes (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:replay) (ns:list FF.pac_node)
  : Tot (option replay)
val lemma_initial (v:nat -> int) (p:pos) : Lemma (Core.values_ok v p initial.core)
val lemma_step (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
  (m:FF.model base schema p) (rho:V.environment base (S.signature schema) [])
  (v:nat -> int) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:replay) (n:FF.pac_node) (r':replay)
  : Lemma (requires D.scoped_args [] lits /\ FF.tree_ok schema p m rho v eqs /\
                    FF.none_true schema p m rho lits /\ Core.values_ok v p r.core /\
                    step p nvars eqs sup lits r n == Some r')
          (ensures Core.values_ok v p r'.core)
val lemma_replay_nodes (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
  (m:FF.model base schema p) (rho:V.environment base (S.signature schema) [])
  (v:nat -> int) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:replay) (ns:list FF.pac_node) (r':replay)
  : Lemma (requires D.scoped_args [] lits /\ FF.tree_ok schema p m rho v eqs /\
                    FF.none_true schema p m rho lits /\ Core.values_ok v p r.core /\
                    replay_nodes p nvars eqs sup lits r ns == Some r')
          (ensures Core.values_ok v p r'.core)
val lemma_add_description (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:replay) (a b:int)
  : Lemma (step p nvars eqs sup lits r (FF.PacAdd a b) ==
           (match Core.add p r.core a b with
            | None -> None
            | Some core -> Some { core = core; used = r.used }))
val lemma_input_description (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:replay) (j:int)
  : Lemma (step p nvars eqs sup lits r (FF.PacInput j) ==
           (if j < 0 then None else
            match IX.index_get eqs j with
            | Some (q, FF.Definition) ->
              (match Core.input p r.core q with
               | None -> None
               | Some core -> Some { core = core; used = r.used })
            | Some (q, FF.Premise k l) ->
              if IX.index_get sup k <> Some true || not (Witness.complementary_in l lits)
              then None
              else (match Core.input p r.core q with
                    | None -> None
                    | Some core -> Some { core = core; used = IX.index_put r.used k true })
            | _ -> None))
val lemma_mul_description (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:replay)
  (source:int) (c:expr) (fs:list int)
  : Lemma (step p nvars eqs sup lits r (FF.PacMul source c fs) ==
           (match FF.numeral c, FF.variables nvars 0 fs with
            | Some (pc, k), Some vs ->
              if pc <> p then None
              else (match Core.scale p r.core source (Monomial.compress vs) k with
                    | None -> None
                    | Some core -> Some { core = core; used = r.used })
            | _, _ -> None))
val lemma_replay_nodes_description (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:replay) (ns:list FF.pac_node)
  : Lemma (replay_nodes p nvars eqs sup lits r ns ==
           (match ns with
            | [] -> Some r
            | n :: rest ->
              (match step p nvars eqs sup lits r n with
               | None -> None
               | Some r' -> replay_nodes p nvars eqs sup lits r' rest)))
