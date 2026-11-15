module Z3IndependentFiniteFieldCompactPacMetered

open Z3AstTheory
module FF = Z3SortedFiniteField
module IX = Z3ProofIndex
module Core = Z3IndependentFiniteFieldCompactReplay
module Metered = Z3IndependentFiniteFieldCompactMetered
module Pac = Z3IndependentFiniteFieldCompactPac
module Witness = Z3IndependentFiniteFieldWitness
module Index = Z3IndependentProofIndex
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module D = Z3ExprScope
module Monomial = Z3IndependentFiniteFieldMonomial

val add_step_metered (fuel:nat) (p:pos) (r:Pac.replay) (a b:int)
  : Tot (option (option Pac.replay & nat))
val lemma_add_step_metered (fuel:nat) (p:pos) (nvars:nat)
  (eqs:IX.index_tree FF.equation) (sup:IX.index_tree bool) (lits:list expr)
  (r:Pac.replay) (a b:int)
  : Lemma (match add_step_metered fuel p r a b with
           | None -> fuel < Metered.add_bound r.core a b
           | Some (result, work) ->
             result == Pac.step p nvars eqs sup lits r (FF.PacAdd a b) /\
             0 < work /\ work <= fuel /\ work <= Metered.add_bound r.core a b)
val lemma_add_step_values_ok (v:nat -> int) (p:pos) (fuel:nat)
  (r r':Pac.replay) (a b:int) (work:nat)
  : Lemma (requires Core.values_ok v p r.core /\
                    add_step_metered fuel p r a b == Some (Some r', work))
          (ensures Core.values_ok v p r'.core)
val complementary_metered (fuel:nat) (l:expr) (lits:list expr)
  : Tot (option (bool & nat))
val lemma_complementary_metered (fuel:nat) (l:expr) (lits:list expr)
  : Lemma (match complementary_metered fuel l lits with
           | None -> fuel < FStar.List.Tot.length lits + 1
           | Some (result, work) ->
             result == Witness.complementary_in l lits /\ 0 < work /\
             work <= fuel /\ work <= FStar.List.Tot.length lits + 1)
val input_step_bound (eqs:IX.index_tree FF.equation) (lits:list expr) (r:Pac.replay) (j:int)
  : GTot nat
val input_step_metered (fuel:nat) (p:pos) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:Pac.replay) (j:int)
  : Tot (option (option Pac.replay & nat))
val lemma_input_step_metered (fuel:nat) (p:pos) (nvars:nat)
  (eqs:IX.index_tree FF.equation) (sup:IX.index_tree bool) (lits:list expr)
  (r:Pac.replay) (j:int)
  : Lemma (match input_step_metered fuel p eqs sup lits r j with
           | None -> fuel < input_step_bound eqs lits r j
           | Some (result, work) ->
             result == Pac.step p nvars eqs sup lits r (FF.PacInput j) /\
             0 < work /\ work <= fuel /\ work <= input_step_bound eqs lits r j)
val lemma_input_step_values_ok (#base:sort -> Type0) (schema:S.checked_schema)
  (p:pos) (m:FF.model base schema p) (rho:V.environment base (S.signature schema) [])
  (v:nat -> int) (fuel:nat) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r r':Pac.replay) (j:int) (work:nat)
  : Lemma (requires D.scoped_args [] lits /\ FF.tree_ok schema p m rho v eqs /\
                    FF.none_true schema p m rho lits /\ Core.values_ok v p r.core /\
                    input_step_metered fuel p eqs sup lits r j == Some (Some r', work))
          (ensures Core.values_ok v p r'.core)
val variables_metered (fuel:nat) (n:nat) (previous:int) (fs:list int)
  : Tot (option (option (list nat) & nat))
val lemma_variables_metered (fuel:nat) (n:nat) (previous:int) (fs:list int)
  : Lemma (match variables_metered fuel n previous fs with
           | None -> fuel < FStar.List.Tot.length fs + 1
           | Some (result, work) ->
             result == FF.variables n previous fs /\ 0 < work /\
             work <= fuel /\ work <= FStar.List.Tot.length fs + 1 /\
             (match result with
              | None -> True
              | Some vs -> FStar.List.Tot.length vs == FStar.List.Tot.length fs))
val mul_step_bound (nvars:nat) (r:Pac.replay) (source:int) (fs:list int) : GTot nat
val mul_step_metered (fuel:nat) (p:pos) (nvars:nat) (r:Pac.replay)
  (source:int) (c:expr) (fs:list int) : Tot (option (option Pac.replay & nat))
val lemma_mul_step_metered (fuel:nat) (p:pos) (nvars:nat)
  (eqs:IX.index_tree FF.equation) (sup:IX.index_tree bool) (lits:list expr)
  (r:Pac.replay) (source:int) (c:expr) (fs:list int)
  : Lemma (match mul_step_metered fuel p nvars r source c fs with
           | None -> fuel < mul_step_bound nvars r source fs
           | Some (result, work) ->
             result == Pac.step p nvars eqs sup lits r (FF.PacMul source c fs) /\
             0 < work /\ work <= fuel /\ work <= mul_step_bound nvars r source fs)
val lemma_mul_step_values_ok (#base:sort -> Type0) (schema:S.checked_schema)
  (p:pos) (m:FF.model base schema p) (rho:V.environment base (S.signature schema) [])
  (v:nat -> int) (fuel:nat) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r r':Pac.replay) (source:int)
  (c:expr) (fs:list int) (work:nat)
  : Lemma (requires D.scoped_args [] lits /\ FF.tree_ok schema p m rho v eqs /\
                    FF.none_true schema p m rho lits /\ Core.values_ok v p r.core /\
                    mul_step_metered fuel p nvars r source c fs == Some (Some r', work))
          (ensures Core.values_ok v p r'.core)
val step_bound (nvars:nat) (eqs:IX.index_tree FF.equation) (lits:list expr)
  (r:Pac.replay) (n:FF.pac_node) : GTot nat
val step_metered (fuel:nat) (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:Pac.replay) (n:FF.pac_node)
  : Tot (option (option Pac.replay & nat))
val lemma_step_metered (fuel:nat) (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:Pac.replay) (n:FF.pac_node)
  : Lemma (match step_metered fuel p nvars eqs sup lits r n with
           | None -> fuel < step_bound nvars eqs lits r n
           | Some (result, work) ->
             result == Pac.step p nvars eqs sup lits r n /\ 0 < work /\
             work <= fuel /\ work <= step_bound nvars eqs lits r n)
val replay_bound (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:Pac.replay) (ns:list FF.pac_node)
  : GTot nat
val replay_nodes_metered (fuel:nat) (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:Pac.replay) (ns:list FF.pac_node)
  : Tot (option (option Pac.replay & nat))
val lemma_replay_nodes_metered (fuel:nat) (p:pos) (nvars:nat)
  (eqs:IX.index_tree FF.equation) (sup:IX.index_tree bool) (lits:list expr)
  (r:Pac.replay) (ns:list FF.pac_node)
  : Lemma (match replay_nodes_metered fuel p nvars eqs sup lits r ns with
           | None -> fuel < replay_bound p nvars eqs sup lits r ns
           | Some (result, work) ->
             result == Pac.replay_nodes p nvars eqs sup lits r ns /\
             work <= fuel /\ work <= replay_bound p nvars eqs sup lits r ns)
val lemma_replay_nodes_values_ok (#base:sort -> Type0) (schema:S.checked_schema)
  (p:pos) (m:FF.model base schema p) (rho:V.environment base (S.signature schema) [])
  (v:nat -> int) (fuel:nat) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r r':Pac.replay)
  (ns:list FF.pac_node) (work:nat)
  : Lemma (requires D.scoped_args [] lits /\ FF.tree_ok schema p m rho v eqs /\
                    FF.none_true schema p m rho lits /\ Core.values_ok v p r.core /\
                    replay_nodes_metered fuel p nvars eqs sup lits r ns == Some (Some r', work))
          (ensures Core.values_ok v p r'.core)

val unit_root_bound (s:Core.state) (root:int) : GTot nat
val unit_root_metered (fuel:nat) (s:Core.state) (root:int)
  : Tot (option (bool & nat))
val lemma_unit_root_metered (fuel:nat) (s:Core.state) (root:int)
  : Lemma (match unit_root_metered fuel s root with
           | None -> fuel < unit_root_bound s root
           | Some (result, work) ->
             result == Core.unit_root s root /\ 0 < work /\
             work <= fuel /\ work <= unit_root_bound s root)
val all_used_bound (support:list int) : GTot nat
val all_used_metered (fuel:nat) (used:IX.index_tree bool) (support:list int)
  : Tot (option (bool & nat))
val lemma_all_used_metered (fuel:nat) (used:IX.index_tree bool) (support:list int)
  : Lemma (match all_used_metered fuel used support with
           | None -> fuel < all_used_bound support
           | Some (result, work) ->
             result == FF.all_used used support /\ 0 < work /\
             work <= fuel /\ work <= all_used_bound support)
val finalize_bound (r:Pac.replay) (root:int) (support:list int) : GTot nat
val finalize_metered (fuel:nat) (r:Pac.replay) (root:int) (support:list int)
  : Tot (option (bool & nat))
val lemma_finalize_metered (fuel:nat) (r:Pac.replay) (root:int) (support:list int)
  : Lemma (match finalize_metered fuel r root support with
           | None -> fuel < finalize_bound r root support
           | Some (result, work) ->
             result == (Core.unit_root r.core root && FF.all_used r.used support) /\
             0 < work /\ work <= fuel /\ work <= finalize_bound r root support)
