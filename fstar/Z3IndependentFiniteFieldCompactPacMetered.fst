module Z3IndependentFiniteFieldCompactPacMetered

open Z3AstTheory
module FF = Z3SortedFiniteField
module IX = Z3ProofIndex
module Core = Z3IndependentFiniteFieldCompactReplay
module Metered = Z3IndependentFiniteFieldCompactMetered
module Pac = Z3IndependentFiniteFieldCompactPac
module Witness = Z3IndependentFiniteFieldWitness
module PT = Z3ProofTheory
module L = FStar.List.Tot
module Index = Z3IndependentProofIndex
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module D = Z3ExprScope
module Monomial = Z3IndependentFiniteFieldMonomial

let add_step_metered (fuel:nat) (p:pos) (r:Pac.replay) (a b:int)
  : Tot (option (option Pac.replay & nat)) =
  match Metered.add_metered fuel p r.core a b with
  | None -> None
  | Some (None, work) -> Some (None, work)
  | Some (Some core, work) -> Some (Some { Pac.core = core; Pac.used = r.used }, work)

let lemma_add_step_metered (fuel:nat) (p:pos) (nvars:nat)
  (eqs:IX.index_tree FF.equation) (sup:IX.index_tree bool) (lits:list expr)
  (r:Pac.replay) (a b:int)
  : Lemma (match add_step_metered fuel p r a b with
           | None -> fuel < Metered.add_bound r.core a b
           | Some (result, work) ->
             result == Pac.step p nvars eqs sup lits r (FF.PacAdd a b) /\
             0 < work /\ work <= fuel /\ work <= Metered.add_bound r.core a b) =
  Metered.lemma_add_metered fuel p r.core a b;
  Pac.lemma_add_description p nvars eqs sup lits r a b

let lemma_add_step_values_ok (v:nat -> int) (p:pos) (fuel:nat)
  (r r':Pac.replay) (a b:int) (work:nat)
  : Lemma (requires Core.values_ok v p r.core /\
                    add_step_metered fuel p r a b == Some (Some r', work))
          (ensures Core.values_ok v p r'.core) =
  match Metered.add_metered fuel p r.core a b with
  | Some (Some core, w) -> Metered.lemma_add_values_ok v p fuel r.core core a b w
  | _ -> ()

let rec complementary_metered (fuel:nat) (l:expr) (lits:list expr)
  : Tot (option (bool & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match lits with
    | [] -> Some (false, 1)
    | x :: rest ->
      if PT.is_not x = Some l || (PT.is_not l = Some x && get_sort x = bool_sort)
      then Some (true, 1)
      else
        match complementary_metered (fuel - 1) l rest with
        | None -> None
        | Some (result, work) -> Some (result, work + 1)

let rec lemma_complementary_metered (fuel:nat) (l:expr) (lits:list expr)
  : Lemma (match complementary_metered fuel l lits with
           | None -> fuel < L.length lits + 1
           | Some (result, work) ->
             result == Witness.complementary_in l lits /\ 0 < work /\
             work <= fuel /\ work <= L.length lits + 1)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match lits with
    | [] -> ()
    | x :: rest ->
      if PT.is_not x <> Some l && (PT.is_not l <> Some x || get_sort x <> bool_sort)
      then lemma_complementary_metered (fuel - 1) l rest

let input_step_bound (eqs:IX.index_tree FF.equation) (lits:list expr) (r:Pac.replay) (j:int)
  : GTot nat =
  if j < 0 then 1
  else
    let extra:nat =
    match IX.index_get eqs j with
     | Some (q, FF.Definition) -> Metered.input_bound r.core q
     | Some (q, FF.Premise k _) ->
       2 * Index.depth k + L.length lits + 1 + Metered.input_bound r.core q
     | _ -> 0
    in 1 + Index.depth j + extra

let lemma_input_step_bound_floor (eqs:IX.index_tree FF.equation)
  (lits:list expr) (r:Pac.replay) (j:int)
  : Lemma (input_step_bound eqs lits r j >= 1 /\
           (j >= 0 ==> input_step_bound eqs lits r j >= 1 + Index.depth j)) =
  if j >= 0 then
    match IX.index_get eqs j with
    | Some (_, FF.Definition) -> ()
    | Some (_, FF.Premise _ _) -> ()
    | _ -> ()

let input_step_metered (fuel:nat) (p:pos) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:Pac.replay) (j:int)
  : Tot (option (option Pac.replay & nat)) =
  if fuel = 0 then None
  else if j < 0 then Some (None, 1)
  else
    let f0 = fuel - 1 in
    Index.lemma_get_metered f0 eqs j;
    match Index.get_metered f0 eqs j with
    | None -> None
    | Some (Some (q, FF.Definition), we) ->
      let f1 = f0 - we in
      Metered.lemma_input_metered f1 p r.core q;
      (match Metered.input_metered f1 p r.core q with
       | None -> None
       | Some (None, wq) -> Some (None, 1 + we + wq)
       | Some (Some core, wq) ->
         Some (Some { Pac.core = core; Pac.used = r.used }, 1 + we + wq))
    | Some (Some (q, FF.Premise k l), we) ->
      let f1 = f0 - we in
      Index.lemma_get_metered f1 sup k;
      (match Index.get_metered f1 sup k with
       | None -> None
       | Some (supported, ws) ->
         if supported <> Some true then Some (None, 1 + we + ws)
         else
           let f2 = f1 - ws in
           lemma_complementary_metered f2 l lits;
           match complementary_metered f2 l lits with
           | None -> None
           | Some (false, wl) -> Some (None, 1 + we + ws + wl)
           | Some (true, wl) ->
             let f3 = f2 - wl in
             Metered.lemma_input_metered f3 p r.core q;
             match Metered.input_metered f3 p r.core q with
             | None -> None
             | Some (None, wq) -> Some (None, 1 + we + ws + wl + wq)
             | Some (Some core, wq) ->
               match Index.put_metered (f3 - wq) r.used k true with
               | None -> None
               | Some (used, wu) ->
                 Some (Some { Pac.core = core; Pac.used = used }, 1 + we + ws + wl + wq + wu))
    | Some (_, we) -> Some (None, 1 + we)

let lemma_input_step_metered (fuel:nat) (p:pos) (nvars:nat)
  (eqs:IX.index_tree FF.equation) (sup:IX.index_tree bool) (lits:list expr)
  (r:Pac.replay) (j:int)
  : Lemma (match input_step_metered fuel p eqs sup lits r j with
           | None -> fuel < input_step_bound eqs lits r j
           | Some (result, work) ->
             result == Pac.step p nvars eqs sup lits r (FF.PacInput j) /\
             0 < work /\ work <= fuel /\ work <= input_step_bound eqs lits r j) =
  lemma_input_step_bound_floor eqs lits r j;
  Pac.lemma_input_description p nvars eqs sup lits r j;
  if fuel > 0 && j >= 0 then (
    let f0 = fuel - 1 in
    Index.lemma_get_metered f0 eqs j;
    match Index.get_metered f0 eqs j with
    | Some (Some (q, FF.Definition), we) ->
      Metered.lemma_input_metered (f0 - we) p r.core q
    | Some (Some (q, FF.Premise k l), we) ->
      let f1 = f0 - we in
      Index.lemma_get_metered f1 sup k;
      (match Index.get_metered f1 sup k with
       | Some (Some true, ws) ->
         let f2 = f1 - ws in
         lemma_complementary_metered f2 l lits;
         (match complementary_metered f2 l lits with
          | Some (true, wl) ->
            let f3 = f2 - wl in
            Metered.lemma_input_metered f3 p r.core q;
            (match Metered.input_metered f3 p r.core q with
             | Some (Some _, wq) -> Index.lemma_put_metered (f3 - wq) r.used k true
             | _ -> ())
          | _ -> ())
       | _ -> ())
    | _ -> ())

let lemma_input_step_values_ok (#base:sort -> Type0) (schema:S.checked_schema)
  (p:pos) (m:FF.model base schema p) (rho:V.environment base (S.signature schema) [])
  (v:nat -> int) (fuel:nat) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r r':Pac.replay) (j:int) (work:nat)
  : Lemma (requires D.scoped_args [] lits /\ FF.tree_ok schema p m rho v eqs /\
                    FF.none_true schema p m rho lits /\ Core.values_ok v p r.core /\
                    input_step_metered fuel p eqs sup lits r j == Some (Some r', work))
          (ensures Core.values_ok v p r'.core) =
  lemma_input_step_metered fuel p nvars eqs sup lits r j;
  Pac.lemma_step schema p m rho v nvars eqs sup lits r (FF.PacInput j) r'

let rec variables_metered (fuel:nat) (n:nat) (previous:int) (fs:list int)
  : Tot (option (option (list nat) & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match fs with
    | [] -> Some (Some [], 1)
    | f :: rest ->
      if f < 0 || f < previous || f >= n then Some (None, 1)
      else
        match variables_metered (fuel - 1) n f rest with
        | None -> None
        | Some (None, work) -> Some (None, work + 1)
        | Some (Some vs, work) -> Some (Some (f :: vs), work + 1)

let rec lemma_variables_metered (fuel:nat) (n:nat) (previous:int) (fs:list int)
  : Lemma (match variables_metered fuel n previous fs with
           | None -> fuel < L.length fs + 1
           | Some (result, work) ->
             result == FF.variables n previous fs /\ 0 < work /\
             work <= fuel /\ work <= L.length fs + 1 /\
             (match result with None -> True | Some vs -> L.length vs == L.length fs))
          (decreases fuel) =
  if fuel > 0 then
    match fs with
    | [] -> ()
    | f :: rest ->
      if 0 <= f && previous <= f && f < n then
        lemma_variables_metered (fuel - 1) n f rest

let mul_step_bound (nvars:nat) (r:Pac.replay) (source:int) (fs:list int) : GTot nat =
  let extra:nat =
    match FF.variables nvars 0 fs with
    | Some vs -> Metered.scale_bound r.core source (Monomial.compress vs)
    | None -> 0
  in 1 + 2 * (L.length fs + 1) + extra

let lemma_mul_step_bound_floor (nvars:nat) (r:Pac.replay) (source:int) (fs:list int)
  : Lemma (mul_step_bound nvars r source fs >= 1 + 2 * (L.length fs + 1)) =
  match FF.variables nvars 0 fs with
  | Some _ -> ()
  | None -> ()

let mul_step_metered (fuel:nat) (p:pos) (nvars:nat) (r:Pac.replay)
  (source:int) (c:expr) (fs:list int) : Tot (option (option Pac.replay & nat)) =
  if fuel = 0 then None
  else
    match FF.numeral c with
    | None -> Some (None, 1)
    | Some (pc, k) ->
      if pc <> p then Some (None, 1)
      else
        let f0 = fuel - 1 in
        lemma_variables_metered f0 nvars 0 fs;
        match variables_metered f0 nvars 0 fs with
        | None -> None
        | Some (None, wv) -> Some (None, 1 + wv)
        | Some (Some vs, wv) ->
          let f1 = f0 - wv in
          Monomial.lemma_compress_metered f1 vs;
          match Monomial.compress_metered f1 vs with
          | None -> None
          | Some (factor, wc) ->
            let f2 = f1 - wc in
            match Metered.scale_metered f2 p r.core source factor k with
            | None -> None
            | Some (None, ws) -> Some (None, 1 + wv + wc + ws)
            | Some (Some core, ws) ->
              Some (Some { Pac.core = core; Pac.used = r.used }, 1 + wv + wc + ws)

let lemma_mul_step_metered (fuel:nat) (p:pos) (nvars:nat)
  (eqs:IX.index_tree FF.equation) (sup:IX.index_tree bool) (lits:list expr)
  (r:Pac.replay) (source:int) (c:expr) (fs:list int)
  : Lemma (match mul_step_metered fuel p nvars r source c fs with
           | None -> fuel < mul_step_bound nvars r source fs
           | Some (result, work) ->
             result == Pac.step p nvars eqs sup lits r (FF.PacMul source c fs) /\
             0 < work /\ work <= fuel /\ work <= mul_step_bound nvars r source fs) =
  Pac.lemma_mul_description p nvars eqs sup lits r source c fs;
  lemma_mul_step_bound_floor nvars r source fs;
  if fuel > 0 then
    match FF.numeral c with
    | Some (pc, k) ->
      if pc = p then (
        let f0 = fuel - 1 in
        lemma_variables_metered f0 nvars 0 fs;
        match variables_metered f0 nvars 0 fs with
        | Some (Some vs, wv) ->
          let f1 = f0 - wv in
          Monomial.lemma_compress_metered f1 vs;
          (match Monomial.compress_metered f1 vs with
           | Some (factor, wc) ->
             Metered.lemma_scale_metered (f1 - wc) p r.core source factor k
           | None -> ())
        | _ -> ())
    | None -> ()

let lemma_mul_step_values_ok (#base:sort -> Type0) (schema:S.checked_schema)
  (p:pos) (m:FF.model base schema p) (rho:V.environment base (S.signature schema) [])
  (v:nat -> int) (fuel:nat) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r r':Pac.replay) (source:int)
  (c:expr) (fs:list int) (work:nat)
  : Lemma (requires D.scoped_args [] lits /\ FF.tree_ok schema p m rho v eqs /\
                    FF.none_true schema p m rho lits /\ Core.values_ok v p r.core /\
                    mul_step_metered fuel p nvars r source c fs == Some (Some r', work))
          (ensures Core.values_ok v p r'.core) =
  lemma_mul_step_metered fuel p nvars eqs sup lits r source c fs;
  Pac.lemma_step schema p m rho v nvars eqs sup lits r (FF.PacMul source c fs) r'

let step_bound (nvars:nat) (eqs:IX.index_tree FF.equation) (lits:list expr)
  (r:Pac.replay) (n:FF.pac_node) : GTot nat =
  match n with
  | FF.PacInput j -> input_step_bound eqs lits r j
  | FF.PacAdd a b -> Metered.add_bound r.core a b
  | FF.PacMul source _ fs -> mul_step_bound nvars r source fs

let step_metered (fuel:nat) (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:Pac.replay) (n:FF.pac_node)
  : Tot (option (option Pac.replay & nat)) =
  match n with
  | FF.PacInput j -> input_step_metered fuel p eqs sup lits r j
  | FF.PacAdd a b -> add_step_metered fuel p r a b
  | FF.PacMul source c fs -> mul_step_metered fuel p nvars r source c fs

let lemma_step_metered (fuel:nat) (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:Pac.replay) (n:FF.pac_node)
  : Lemma (match step_metered fuel p nvars eqs sup lits r n with
           | None -> fuel < step_bound nvars eqs lits r n
           | Some (result, work) ->
             result == Pac.step p nvars eqs sup lits r n /\ 0 < work /\
             work <= fuel /\ work <= step_bound nvars eqs lits r n) =
  match n with
  | FF.PacInput j -> lemma_input_step_metered fuel p nvars eqs sup lits r j
  | FF.PacAdd a b -> lemma_add_step_metered fuel p nvars eqs sup lits r a b
  | FF.PacMul source c fs ->
    lemma_mul_step_metered fuel p nvars eqs sup lits r source c fs

let rec replay_bound (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:Pac.replay) (ns:list FF.pac_node)
  : GTot nat (decreases ns) =
  match ns with
  | [] -> 0
  | n :: rest ->
    let tail:nat =
      match Pac.step p nvars eqs sup lits r n with
      | None -> 0
      | Some r' -> replay_bound p nvars eqs sup lits r' rest
    in step_bound nvars eqs lits r n + tail

let rec replay_nodes_acc (fuel spent:nat) (p:pos) (nvars:nat)
  (eqs:IX.index_tree FF.equation) (sup:IX.index_tree bool) (lits:list expr)
  (r:Pac.replay) (ns:list FF.pac_node)
  : Tot (option (option Pac.replay & nat)) (decreases ns) =
  match ns with
  | [] -> Some (Some r, spent)
  | n :: rest ->
    lemma_step_metered fuel p nvars eqs sup lits r n;
    match step_metered fuel p nvars eqs sup lits r n with
    | None -> None
    | Some (None, work) -> Some (None, spent + work)
    | Some (Some r', work) ->
      replay_nodes_acc (fuel - work) (spent + work) p nvars eqs sup lits r' rest

let rec lemma_replay_nodes_acc (fuel spent:nat) (p:pos) (nvars:nat)
  (eqs:IX.index_tree FF.equation) (sup:IX.index_tree bool) (lits:list expr)
  (r:Pac.replay) (ns:list FF.pac_node)
  : Lemma (match replay_nodes_acc fuel spent p nvars eqs sup lits r ns with
           | None -> fuel < replay_bound p nvars eqs sup lits r ns
           | Some (result, work) ->
             result == Pac.replay_nodes p nvars eqs sup lits r ns /\
             spent <= work /\ work <= spent + fuel /\
             work - spent <= replay_bound p nvars eqs sup lits r ns)
          (decreases ns) =
  Pac.lemma_replay_nodes_description p nvars eqs sup lits r ns;
  match ns with
  | [] -> ()
  | n :: rest ->
    lemma_step_metered fuel p nvars eqs sup lits r n;
    (match step_metered fuel p nvars eqs sup lits r n with
     | Some (Some r', work) ->
       lemma_replay_nodes_acc (fuel - work) (spent + work)
         p nvars eqs sup lits r' rest
     | _ -> ())

let replay_nodes_metered (fuel:nat) (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:Pac.replay) (ns:list FF.pac_node)
  : Tot (option (option Pac.replay & nat)) =
  replay_nodes_acc fuel 0 p nvars eqs sup lits r ns

let lemma_replay_nodes_metered (fuel:nat) (p:pos) (nvars:nat)
  (eqs:IX.index_tree FF.equation) (sup:IX.index_tree bool) (lits:list expr)
  (r:Pac.replay) (ns:list FF.pac_node)
  : Lemma (match replay_nodes_metered fuel p nvars eqs sup lits r ns with
           | None -> fuel < replay_bound p nvars eqs sup lits r ns
           | Some (result, work) ->
             result == Pac.replay_nodes p nvars eqs sup lits r ns /\
             work <= fuel /\ work <= replay_bound p nvars eqs sup lits r ns) =
  lemma_replay_nodes_acc fuel 0 p nvars eqs sup lits r ns

let lemma_replay_nodes_values_ok (#base:sort -> Type0) (schema:S.checked_schema)
  (p:pos) (m:FF.model base schema p) (rho:V.environment base (S.signature schema) [])
  (v:nat -> int) (fuel:nat) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r r':Pac.replay)
  (ns:list FF.pac_node) (work:nat)
  : Lemma (requires D.scoped_args [] lits /\ FF.tree_ok schema p m rho v eqs /\
                    FF.none_true schema p m rho lits /\ Core.values_ok v p r.core /\
                    replay_nodes_metered fuel p nvars eqs sup lits r ns == Some (Some r', work))
          (ensures Core.values_ok v p r'.core) =
  lemma_replay_nodes_metered fuel p nvars eqs sup lits r ns;
  Pac.lemma_replay_nodes schema p m rho v nvars eqs sup lits r ns r'

let unit_root_bound (s:Core.state) (root:int) : GTot nat =
  if 0 <= root && root < s.Core.next then 1 + Index.depth root else 1

let unit_root_metered (fuel:nat) (s:Core.state) (root:int)
  : Tot (option (bool & nat)) =
  if fuel <= 0 then None
  else if root < 0 || root >= s.Core.next then Some (false, 1)
  else
    match Index.get_metered (fuel - 1) s.Core.values root with
    | None -> None
    | Some (q, work) -> Some (q = Some [([], 1)], work + 1)

let lemma_unit_root_metered (fuel:nat) (s:Core.state) (root:int)
  : Lemma (match unit_root_metered fuel s root with
           | None -> fuel < unit_root_bound s root
           | Some (result, work) ->
             result == Core.unit_root s root /\ 0 < work /\
             work <= fuel /\ work <= unit_root_bound s root) =
  Core.lemma_unit_root_description s root;
  if fuel > 0 && 0 <= root && root < s.Core.next
  then Index.lemma_get_metered (fuel - 1) s.Core.values root

let rec all_used_bound (support:list int) : GTot nat (decreases support) =
  match support with
  | [] -> 1
  | k :: rest -> if k < 0 then 1 else 1 + Index.depth k + all_used_bound rest

let rec all_used_acc (fuel spent:nat) (used:IX.index_tree bool) (support:list int)
  : Tot (option (bool & nat)) (decreases support) =
  if fuel <= 0 then None
  else
    match support with
    | [] -> Some (true, spent + 1)
    | k :: rest ->
      if k < 0 then Some (false, spent + 1)
      else
        let _ = Index.lemma_get_metered (fuel - 1) used k in
        match Index.get_metered (fuel - 1) used k with
        | None -> None
        | Some (value, work) ->
          if value <> Some true then Some (false, spent + 1 + work)
          else all_used_acc (fuel - 1 - work) (spent + 1 + work) used rest

let rec lemma_all_used_acc (fuel spent:nat) (used:IX.index_tree bool) (support:list int)
  : Lemma (match all_used_acc fuel spent used support with
           | None -> fuel < all_used_bound support
           | Some (result, work) ->
             result == FF.all_used used support /\ spent < work /\
             work <= spent + fuel /\ work - spent <= all_used_bound support)
          (decreases support) =
  if fuel > 0 then
    match support with
    | [] -> ()
    | k :: rest ->
      if k >= 0 then (
        Index.lemma_get_metered (fuel - 1) used k;
        match Index.get_metered (fuel - 1) used k with
        | Some (Some true, work) ->
          lemma_all_used_acc (fuel - 1 - work) (spent + 1 + work) used rest
        | _ -> ())

let all_used_metered (fuel:nat) (used:IX.index_tree bool) (support:list int)
  : Tot (option (bool & nat)) =
  all_used_acc fuel 0 used support

let lemma_all_used_metered (fuel:nat) (used:IX.index_tree bool) (support:list int)
  : Lemma (match all_used_metered fuel used support with
           | None -> fuel < all_used_bound support
           | Some (result, work) ->
             result == FF.all_used used support /\ 0 < work /\
             work <= fuel /\ work <= all_used_bound support) =
  lemma_all_used_acc fuel 0 used support

let finalize_bound (r:Pac.replay) (root:int) (support:list int) : GTot nat =
  unit_root_bound r.Pac.core root + all_used_bound support

let finalize_metered (fuel:nat) (r:Pac.replay) (root:int) (support:list int)
  : Tot (option (bool & nat)) =
  lemma_unit_root_metered fuel r.Pac.core root;
  match unit_root_metered fuel r.Pac.core root with
  | None -> None
  | Some (false, work) -> Some (false, work)
  | Some (true, work) ->
    match all_used_metered (fuel - work) r.Pac.used support with
    | None -> None
    | Some (result, extra) -> Some (result, work + extra)

let lemma_finalize_metered (fuel:nat) (r:Pac.replay) (root:int) (support:list int)
  : Lemma (match finalize_metered fuel r root support with
           | None -> fuel < finalize_bound r root support
           | Some (result, work) ->
             result == (Core.unit_root r.core root && FF.all_used r.used support) /\
             0 < work /\ work <= fuel /\ work <= finalize_bound r root support) =
  lemma_unit_root_metered fuel r.Pac.core root;
  match unit_root_metered fuel r.Pac.core root with
  | Some (true, work) -> lemma_all_used_metered (fuel - work) r.Pac.used support
  | _ -> ()
