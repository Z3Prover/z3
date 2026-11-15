module Z3IndependentFiniteFieldCompactPac

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module D = Z3ExprScope
module FF = Z3SortedFiniteField
module IX = Z3ProofIndex
module Core = Z3IndependentFiniteFieldCompactReplay
module Monomial = Z3IndependentFiniteFieldMonomial
module Witness = Z3IndependentFiniteFieldWitness

let initial : replay = { core = Core.initial; used = IX.Empty }

let step (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:replay) (n:FF.pac_node)
  : Tot (option replay) =
  match n with
  | FF.PacInput j ->
    if j < 0 then None else
    (match IX.index_get eqs j with
     | Some (q, FF.Definition) ->
       (match Core.input p r.core q with
        | Some s -> Some { core = s; used = r.used }
        | None -> None)
     | Some (q, FF.Premise k l) ->
       if IX.index_get sup k <> Some true || not (Witness.complementary_in l lits) then None
       else
         (match Core.input p r.core q with
          | Some s -> Some { core = s; used = IX.index_put r.used k true }
          | None -> None)
     | _ -> None)
  | FF.PacAdd a b ->
    (match Core.add p r.core a b with
     | Some s -> Some { core = s; used = r.used }
     | None -> None)
  | FF.PacMul source c fs ->
    (match FF.numeral c, FF.variables nvars 0 fs with
     | Some (pc, k), Some vs ->
       if pc <> p then None
       else
         (match Core.scale p r.core source (Monomial.compress vs) k with
          | Some s -> Some { core = s; used = r.used }
          | None -> None)
     | _, _ -> None)

let rec replay_nodes (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:replay) (ns:list FF.pac_node)
  : Tot (option replay) (decreases ns) =
  match ns with
  | [] -> Some r
  | n :: rest ->
    (match step p nvars eqs sup lits r n with
     | None -> None
     | Some r' -> replay_nodes p nvars eqs sup lits r' rest)

let lemma_initial (v:nat -> int) (p:pos) : Lemma (Core.values_ok v p initial.core) =
  Core.lemma_initial v p

let lemma_step (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
  (m:FF.model base schema p) (rho:V.environment base (S.signature schema) [])
  (v:nat -> int) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:replay) (n:FF.pac_node) (r':replay)
  : Lemma (requires D.scoped_args [] lits /\ FF.tree_ok schema p m rho v eqs /\
                    FF.none_true schema p m rho lits /\ Core.values_ok v p r.core /\
                    step p nvars eqs sup lits r n == Some r')
          (ensures Core.values_ok v p r'.core) =
  match n with
  | FF.PacInput j ->
    (match IX.index_get eqs j with
     | Some (q, FF.Definition) ->
       FF.lemma_tree_get schema p m rho v eqs j (q, FF.Definition);
       Core.lemma_input v p r.core r'.core q
     | Some (q, FF.Premise k l) ->
       FF.lemma_tree_get schema p m rho v eqs j (q, FF.Premise k l);
       Witness.lemma_complementary_in schema p m rho l lits;
       Core.lemma_input v p r.core r'.core q
     | _ -> ())
  | FF.PacAdd a b -> Core.lemma_add v p r.core r'.core a b
  | FF.PacMul source c fs ->
    let (_, k) = Some?.v (FF.numeral c) in
    let vs = Some?.v (FF.variables nvars 0 fs) in
    Core.lemma_scale v p r.core r'.core source (Monomial.compress vs) k

let rec lemma_replay_nodes (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
  (m:FF.model base schema p) (rho:V.environment base (S.signature schema) [])
  (v:nat -> int) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:replay) (ns:list FF.pac_node) (r':replay)
  : Lemma (requires D.scoped_args [] lits /\ FF.tree_ok schema p m rho v eqs /\
                    FF.none_true schema p m rho lits /\ Core.values_ok v p r.core /\
                    replay_nodes p nvars eqs sup lits r ns == Some r')
          (ensures Core.values_ok v p r'.core) (decreases ns) =
  match ns with
  | [] -> ()
  | n :: rest ->
    let r1 = Some?.v (step p nvars eqs sup lits r n) in
    lemma_step schema p m rho v nvars eqs sup lits r n r1;
    lemma_replay_nodes schema p m rho v nvars eqs sup lits r1 rest r'

let lemma_add_description (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:replay) (a b:int)
  : Lemma (step p nvars eqs sup lits r (FF.PacAdd a b) ==
           (match Core.add p r.core a b with
            | None -> None
            | Some core -> Some { core = core; used = r.used })) = ()

let lemma_input_description (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
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
            | _ -> None)) = ()

let lemma_mul_description (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:replay)
  (source:int) (c:expr) (fs:list int)
  : Lemma (step p nvars eqs sup lits r (FF.PacMul source c fs) ==
           (match FF.numeral c, FF.variables nvars 0 fs with
            | Some (pc, k), Some vs ->
              if pc <> p then None
              else (match Core.scale p r.core source (Monomial.compress vs) k with
                    | None -> None
                    | Some core -> Some { core = core; used = r.used })
            | _, _ -> None)) = ()

let lemma_replay_nodes_description (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:replay) (ns:list FF.pac_node)
  : Lemma (replay_nodes p nvars eqs sup lits r ns ==
           (match ns with
            | [] -> Some r
            | n :: rest ->
              (match step p nvars eqs sup lits r n with
               | None -> None
               | Some r' -> replay_nodes p nvars eqs sup lits r' rest))) = ()
