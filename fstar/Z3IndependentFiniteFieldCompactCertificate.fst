module Z3IndependentFiniteFieldCompactCertificate

open Z3AstTheory
module E = FStar.Math.Euclid
module S = Z3DatatypeSignature
module D = Z3ExprScope
module FF = Z3SortedFiniteField
module Canonical = Z3CanonicalOps
module SS = Z3SortedSemantics
module IX = Z3ProofIndex
module Index = Z3IndependentProofIndex
module L = FStar.List.Tot
module Witness = Z3IndependentFiniteFieldWitness
module Core = Z3IndependentFiniteFieldCompactReplay
module Pac = Z3IndependentFiniteFieldCompactPac
module Metered = Z3IndependentFiniteFieldCompactPacMetered

let check_for_prime (p:int{E.is_prime p}) (c:FF.certificate) (e:expr) : Tot bool =
  let n = L.length c.FF.pac_premises in
  if n = 0 || n > FF.max_premises || L.length c.FF.pac_nodes > FF.max_nodes ||
     FF.find_modulus_args c.FF.pac_premises <> Some p then false
  else
    (match Witness.bind p 0 FF.empty_encoding c.FF.pac_premises,
           FF.support_tree n (-1) IX.Empty c.FF.pac_support with
     | Some st, Some sup ->
       let eqs = FF.index_equations IX.Empty
                   (L.length st.FF.equations - 1) st.FF.equations in
       (match Pac.replay_nodes p (L.length st.FF.terms) eqs sup
                (FF.clause_literals e) Pac.initial c.FF.pac_nodes with
        | Some r -> Core.unit_root r.Pac.core c.FF.pac_root &&
                    FF.all_used r.Pac.used c.FF.pac_support
        | None -> false)
     | _, _ -> false)

let check_with_evidence (c:FF.certificate) (e:expr)
  (evidence:option (int & list int)) : Tot bool =
  let n = L.length c.FF.pac_premises in
  if n = 0 || n > FF.max_premises || L.length c.FF.pac_nodes > FF.max_nodes then false
  else match FF.find_modulus_args c.FF.pac_premises with
    | Some p -> if Witness.prime_with_evidence p evidence then check_for_prime p c e else false
    | None -> false

let check (c:FF.certificate) (e:expr) : Tot bool =
  check_with_evidence c e None

let lemma_check_for_prime_sound (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p) (c:FF.certificate) (e:expr)
  : Lemma (requires D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\ check_for_prime p c e)
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e) =
  let rho = SS.empty_environment (S.signature schema) in
  let st = Some?.v (Witness.bind p 0 FF.empty_encoding c.FF.pac_premises) in
  Witness.lemma_bind_scoped p 0 FF.empty_encoding c.FF.pac_premises st;
  let sup = Some?.v
    (FF.support_tree (L.length c.FF.pac_premises) (-1) IX.Empty c.FF.pac_support) in
  let v = Witness.valuation schema p m rho st.FF.terms in
  let eqs = FF.index_equations IX.Empty (L.length st.FF.equations - 1) st.FF.equations in
  let lits = FF.clause_literals e in
  let r = Some?.v
    (Pac.replay_nodes p (L.length st.FF.terms) eqs sup lits Pac.initial c.FF.pac_nodes) in
  FF.lemma_prefix_refl st.FF.terms;
  Witness.lemma_bind schema p m rho 0 FF.empty_encoding c.FF.pac_premises st st.FF.terms;
  FF.lemma_index_equations schema p m rho v IX.Empty (L.length st.FF.equations - 1) st.FF.equations;
  FF.lemma_clause_literals_scoped e;
  Pac.lemma_initial v p;
  let aux () : Lemma
    (requires not (SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] rho e))
    (ensures False) =
    FF.lemma_clause_false_literals schema p m rho e;
    Pac.lemma_replay_nodes schema p m rho v (L.length st.FF.terms) eqs sup lits
      Pac.initial c.FF.pac_nodes r;
    Core.lemma_unit_root v p r.Pac.core c.FF.pac_root
  in FStar.Classical.move_requires aux ()

let lemma_check_with_evidence_sound (#base:sort -> Type0) (schema:S.checked_schema)
  (p:pos) (m:FF.model base schema p) (c:FF.certificate) (e:expr)
  (evidence:option (int & list int))
  : Lemma (requires FF.find_modulus_args c.FF.pac_premises == Some p /\
                    D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\ check_with_evidence c e evidence)
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e) =
  assert (Witness.prime_with_evidence p evidence);
  lemma_check_for_prime_sound schema p m c e

let lemma_check_sound (#base:sort -> Type0) (schema:S.checked_schema)
  (p:pos) (m:FF.model base schema p) (c:FF.certificate) (e:expr)
  : Lemma (requires FF.find_modulus_args c.FF.pac_premises == Some p /\
                    D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\ check c e)
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e) =
  lemma_check_with_evidence_sound schema p m c e None

let rec support_tree_bound (n previous:int) (support:list int)
  : GTot pos (decreases support) =
  match support with
  | [] -> 1
  | k :: rest ->
    if 0 <= k && previous < k && k < n
    then 1 + Index.depth k + support_tree_bound n k rest
    else 1

let rec support_tree_acc (fuel spent:nat) (n previous:int)
  (tree:IX.index_tree bool) (support:list int)
  : Tot (option (option (IX.index_tree bool) & nat)) (decreases support) =
  if fuel <= 0 then None
  else match support with
    | [] -> Some (Some tree, spent + 1)
    | k :: rest ->
      if 0 <= k && previous < k && k < n then
        let _ = Index.lemma_put_metered (fuel - 1) tree k true in
        match Index.put_metered (fuel - 1) tree k true with
        | None -> None
        | Some (next, work) ->
          support_tree_acc (fuel - 1 - work) (spent + 1 + work) n k next rest
      else Some (None, spent + 1)

let rec lemma_support_tree_acc (fuel spent:nat) (n previous:int)
  (tree:IX.index_tree bool) (support:list int)
  : Lemma (match support_tree_acc fuel spent n previous tree support with
           | None -> fuel < support_tree_bound n previous support
           | Some (result, work) ->
             result == FF.support_tree n previous tree support /\
             work == spent + support_tree_bound n previous support /\
             work <= spent + fuel)
          (decreases support) =
  if fuel > 0 then
    match support with
    | [] -> ()
    | k :: rest ->
      if 0 <= k && previous < k && k < n then (
        Index.lemma_put_metered (fuel - 1) tree k true;
        match Index.put_metered (fuel - 1) tree k true with
        | None -> ()
        | Some (next, work) ->
          lemma_support_tree_acc (fuel - 1 - work) (spent + 1 + work) n k next rest)

let support_tree_metered (fuel:nat) (n previous:int)
  (tree:IX.index_tree bool) (support:list int)
  : Tot (option (option (IX.index_tree bool) & nat)) =
  support_tree_acc fuel 0 n previous tree support

let lemma_support_tree_metered (fuel:nat) (n previous:int)
  (tree:IX.index_tree bool) (support:list int)
  : Lemma (match support_tree_metered fuel n previous tree support with
           | None -> fuel < support_tree_bound n previous support
           | Some (result, work) ->
             result == FF.support_tree n previous tree support /\
             work == support_tree_bound n previous support /\ work <= fuel) =
  lemma_support_tree_acc fuel 0 n previous tree support

let rec index_equations_bound (k:int) (equations:list FF.equation)
  : GTot pos (decreases equations) =
  match equations with
  | [] -> 1
  | _ :: rest ->
    if k < 0 then 1
    else 1 + Index.depth k + index_equations_bound (k - 1) rest

let rec index_equations_acc (fuel spent:nat) (tree:IX.index_tree FF.equation)
  (k:int) (equations:list FF.equation)
  : Tot (option (IX.index_tree FF.equation & nat)) (decreases equations) =
  if fuel <= 0 then None
  else match equations with
    | [] -> Some (tree, spent + 1)
    | e :: rest ->
      if k < 0 then Some (tree, spent + 1)
      else
        let _ = Index.lemma_put_metered (fuel - 1) tree k e in
        match Index.put_metered (fuel - 1) tree k e with
        | None -> None
        | Some (next, work) ->
          index_equations_acc (fuel - 1 - work) (spent + 1 + work)
            next (k - 1) rest

let rec lemma_index_equations_acc (fuel spent:nat) (tree:IX.index_tree FF.equation)
  (k:int) (equations:list FF.equation)
  : Lemma (match index_equations_acc fuel spent tree k equations with
           | None -> fuel < index_equations_bound k equations
           | Some (result, work) ->
             result == FF.index_equations tree k equations /\
             work == spent + index_equations_bound k equations /\
             work <= spent + fuel)
          (decreases equations) =
  if fuel > 0 then
    match equations with
    | [] -> ()
    | e :: rest ->
      if k >= 0 then (
        Index.lemma_put_metered (fuel - 1) tree k e;
        match Index.put_metered (fuel - 1) tree k e with
        | None -> ()
        | Some (next, work) ->
          lemma_index_equations_acc (fuel - 1 - work) (spent + 1 + work)
            next (k - 1) rest)

let index_equations_metered (fuel:nat) (tree:IX.index_tree FF.equation)
  (k:int) (equations:list FF.equation)
  : Tot (option (IX.index_tree FF.equation & nat)) =
  index_equations_acc fuel 0 tree k equations

let lemma_index_equations_metered (fuel:nat) (tree:IX.index_tree FF.equation)
  (k:int) (equations:list FF.equation)
  : Lemma (match index_equations_metered fuel tree k equations with
           | None -> fuel < index_equations_bound k equations
           | Some (result, work) ->
             result == FF.index_equations tree k equations /\
             work == index_equations_bound k equations /\ work <= fuel) =
  lemma_index_equations_acc fuel 0 tree k equations

let rec domain_valid (p:int) (domain:list sort) : GTot bool (decreases domain) =
  match domain with
  | [] -> true
  | s :: rest -> sort_eq s (FF.ff_sort p) && domain_valid p rest

let rec lemma_domain_repeated (p:int) (domain:list sort)
  : Lemma (domain_valid p domain ==
           sort_list_eq domain (FF.repeat_sort p (L.length domain)))
          (decreases domain) =
  match domain with
  | [] -> ()
  | _ :: rest -> lemma_domain_repeated p rest

let rec domain_arity_bound (p:int) (domain:list sort)
  : GTot pos (decreases domain) =
  match domain with
  | [] -> 1
  | s :: rest ->
    if sort_eq s (FF.ff_sort p) then 1 + domain_arity_bound p rest else 1

let rec domain_arity_acc (fuel count spent:nat) (p:int) (domain:list sort)
  : Tot (option (option nat & nat)) (decreases domain) =
  if fuel <= 0 then None
  else match domain with
    | [] -> Some (Some count, spent + 1)
    | s :: rest ->
      if sort_eq s (FF.ff_sort p)
      then domain_arity_acc (fuel - 1) (count + 1) (spent + 1) p rest
      else Some (None, spent + 1)

let rec lemma_domain_arity_acc (fuel count spent:nat) (p:int) (domain:list sort)
  : Lemma (match domain_arity_acc fuel count spent p domain with
           | None -> fuel < domain_arity_bound p domain
           | Some (result, work) ->
             result == (if domain_valid p domain then Some (count + L.length domain) else None) /\
             work == spent + domain_arity_bound p domain /\ work <= spent + fuel)
          (decreases domain) =
  if fuel > 0 then
    match domain with
    | [] -> ()
    | s :: rest ->
      if sort_eq s (FF.ff_sort p) then
        lemma_domain_arity_acc (fuel - 1) (count + 1) (spent + 1) p rest

let domain_arity_metered (fuel:nat) (p:int) (domain:list sort)
  : Tot (option (option nat & nat)) =
  domain_arity_acc fuel 0 0 p domain

let lemma_domain_arity_metered (fuel:nat) (p:int) (domain:list sort)
  : Lemma (match domain_arity_metered fuel p domain with
           | None -> fuel < domain_arity_bound p domain
           | Some (result, work) ->
             result == (if sort_list_eq domain (FF.repeat_sort p (L.length domain))
                        then Some (L.length domain) else None) /\
             work == domain_arity_bound p domain /\ work <= fuel) =
  lemma_domain_repeated p domain;
  lemma_domain_arity_acc fuel 0 0 p domain

let operation_of_bound (f:func_decl) : GTot pos =
  match f.int_params, f.interp with
  | [p], Some tag ->
    if p < 2 || not (sort_eq f.range (FF.ff_sort p)) || tag = FF.op_ff_neg then 1
    else if tag = FF.op_ff_add || tag = FF.op_ff_mul || tag = FF.op_ff_bitsum
    then 1 + domain_arity_bound p f.domain
    else 1
  | _, _ -> 1

let operation_of_metered (fuel:nat) (f:func_decl)
  : Tot (option (option (int & decl_kind) & nat)) =
  if fuel <= 0 then None
  else match f.int_params, f.interp with
    | [p], Some tag ->
      if p < 2 || not (sort_eq f.range (FF.ff_sort p)) then Some (None, 1)
      else if tag = FF.op_ff_neg then
        Some ((if sort_list_eq f.domain [FF.ff_sort p]
               then Some (p, FF.op_ff_neg) else None), 1)
      else if tag = FF.op_ff_add || tag = FF.op_ff_mul || tag = FF.op_ff_bitsum then
        let _ = lemma_domain_arity_metered (fuel - 1) p f.domain in
        (match domain_arity_metered (fuel - 1) p f.domain with
         | None -> None
         | Some (arity, work) ->
           Some ((match arity with
                  | Some n -> if n >= 2 then Some (p, tag) else None
                  | None -> None), 1 + work))
      else Some (None, 1)
    | _, _ -> Some (None, 1)

let lemma_operation_of_metered (fuel:nat) (f:func_decl)
  : Lemma (match operation_of_metered fuel f with
           | None -> fuel < operation_of_bound f
           | Some (result, work) ->
             result == FF.operation_of f /\ work == operation_of_bound f /\ work <= fuel) =
  if fuel > 0 then
    match f.int_params, f.interp with
    | [p], Some tag ->
      if p >= 2 && sort_eq f.range (FF.ff_sort p) && tag <> FF.op_ff_neg &&
         (tag = FF.op_ff_add || tag = FF.op_ff_mul || tag = FF.op_ff_bitsum) then
        lemma_domain_arity_metered (fuel - 1) p f.domain
    | _, _ -> ()

let rec arguments_match_bound (p:int) (domain:list sort) (args:list expr)
  : GTot pos (decreases args) =
  match domain, args with
  | _ :: ds, a :: rest ->
    if sort_eq (get_sort a) (FF.ff_sort p)
    then 1 + arguments_match_bound p ds rest else 1
  | _, _ -> 1

let rec arguments_match_acc (fuel spent:nat) (p:int) (domain:list sort) (args:list expr)
  : Tot (option (bool & nat)) (decreases args) =
  if fuel <= 0 then None
  else match domain, args with
    | [], [] -> Some (true, spent + 1)
    | _ :: ds, a :: rest ->
      if sort_eq (get_sort a) (FF.ff_sort p)
      then arguments_match_acc (fuel - 1) (spent + 1) p ds rest
      else Some (false, spent + 1)
    | _, _ -> Some (false, spent + 1)

let rec lemma_arguments_match_acc (fuel spent:nat) (p:int) (domain:list sort) (args:list expr)
  : Lemma (match arguments_match_acc fuel spent p domain args with
           | None -> fuel < arguments_match_bound p domain args
           | Some (result, work) ->
             result == (FF.args_have_sort p args && L.length args = L.length domain) /\
             work == spent + arguments_match_bound p domain args /\ work <= spent + fuel)
          (decreases args) =
  if fuel > 0 then
    match domain, args with
    | _ :: ds, a :: rest ->
      if sort_eq (get_sort a) (FF.ff_sort p) then
        lemma_arguments_match_acc (fuel - 1) (spent + 1) p ds rest
    | _, _ -> ()

let arguments_match_metered (fuel:nat) (p:int) (domain:list sort) (args:list expr)
  : Tot (option (bool & nat)) =
  arguments_match_acc fuel 0 p domain args

let lemma_arguments_match_metered (fuel:nat) (p:int) (domain:list sort) (args:list expr)
  : Lemma (match arguments_match_metered fuel p domain args with
           | None -> fuel < arguments_match_bound p domain args
           | Some (result, work) ->
             result == (FF.args_have_sort p args && L.length args = L.length domain) /\
             work == arguments_match_bound p domain args /\ work <= fuel) =
  lemma_arguments_match_acc fuel 0 p domain args

let operation_at_bound (f:func_decl) (args:list expr) : GTot pos =
  operation_of_bound f +
    (match FF.operation_of f with
     | None -> 0
     | Some (p, _) -> arguments_match_bound p f.domain args)

let operation_at_metered (fuel:nat) (f:func_decl) (args:list expr)
  : Tot (option (option (int & decl_kind) & nat)) =
  let _ = lemma_operation_of_metered fuel f in
  match operation_of_metered fuel f with
  | None -> None
  | Some (None, work) -> Some (None, work)
  | Some (Some (p, op), work) ->
    (match arguments_match_metered (fuel - work) p f.domain args with
     | None -> None
     | Some (valid, extra) ->
       Some ((if valid then Some (p, op) else None), work + extra))

let lemma_operation_at_metered (fuel:nat) (f:func_decl) (args:list expr)
  : Lemma (match operation_at_metered fuel f args with
           | None -> fuel < operation_at_bound f args
           | Some (result, work) ->
             result == FF.operation_at f args /\ work == operation_at_bound f args /\ work <= fuel) =
  lemma_operation_of_metered fuel f;
  match operation_of_metered fuel f with
  | Some (Some (p, _), work) -> lemma_arguments_match_metered (fuel - work) p f.domain args
  | _ -> ()

let modulus_of_bound (e:expr) : GTot pos =
  match FF.numeral e with
  | Some _ -> 1
  | None ->
    match e with
    | App f args -> 1 + operation_at_bound f args
    | _ -> 1

let modulus_of_metered (fuel:nat) (e:expr) : Tot (option (option int & nat)) =
  if fuel <= 0 then None
  else match FF.numeral e with
    | Some (p, _) -> Some (Some p, 1)
    | None ->
      match e with
      | App f args ->
        (match operation_at_metered (fuel - 1) f args with
         | None -> None
         | Some (result, work) ->
           Some ((match result with Some (p, _) -> Some p | None -> None), 1 + work))
      | _ -> Some (None, 1)

let lemma_modulus_of_metered (fuel:nat) (e:expr)
  : Lemma (match modulus_of_metered fuel e with
           | None -> fuel < modulus_of_bound e
           | Some (result, work) ->
             result == FF.modulus_of e /\ work == modulus_of_bound e /\ work <= fuel) =
  if fuel > 0 then
    match FF.numeral e with
    | Some _ -> ()
    | None ->
      match e with
      | App f args -> lemma_operation_at_metered (fuel - 1) f args
      | _ -> ()

let rec modulus_expression_weight (e:expr) : GTot pos (decreases e) =
  match e with
  | App _ args -> 2 + modulus_arguments_weight args
  | _ -> 1

and modulus_arguments_weight (args:list expr) : GTot nat (decreases args) =
  match args with
  | [] -> 0
  | a :: rest -> modulus_expression_weight a + modulus_arguments_weight rest

let rec modulus_pending_weight (pending:list (list expr))
  : GTot nat (decreases pending) =
  match pending with
  | [] -> 0
  | args :: rest -> 1 + modulus_arguments_weight args + modulus_pending_weight rest

let rec modulus_search_result (args:list expr) (pending:list (list expr))
  : GTot (option int) (decreases pending) =
  match FF.find_modulus_args args with
  | Some p -> Some p
  | None ->
    match pending with
    | [] -> None
    | next :: rest -> modulus_search_result next rest

let rec modulus_search_bound (args:list expr) (pending:list (list expr))
  : GTot pos
    (decreases (1 + modulus_arguments_weight args + modulus_pending_weight pending)) =
  match args with
  | [] ->
    (match pending with
     | [] -> 1
     | next :: rest -> 1 + modulus_search_bound next rest)
  | a :: rest ->
    let visit = modulus_of_bound a in
    match FF.modulus_of a with
    | Some _ -> visit
    | None ->
      match a with
      | App _ children -> visit + modulus_search_bound children (rest :: pending)
      | _ -> visit + modulus_search_bound rest pending

let rec modulus_search_acc (fuel spent:nat) (args:list expr) (pending:list (list expr))
  : Tot (option (option int & nat)) (decreases fuel) =
  if fuel <= 0 then None
  else match args with
    | [] ->
      (match pending with
       | [] -> Some (None, spent + 1)
       | next :: rest -> modulus_search_acc (fuel - 1) (spent + 1) next rest)
    | a :: rest ->
      let _ = lemma_modulus_of_metered fuel a in
      match modulus_of_metered fuel a with
      | None -> None
      | Some (Some p, work) -> Some (Some p, spent + work)
      | Some (None, work) ->
        match a with
        | App _ children ->
          modulus_search_acc (fuel - work) (spent + work) children (rest :: pending)
        | _ -> modulus_search_acc (fuel - work) (spent + work) rest pending

let rec lemma_modulus_search_acc (fuel spent:nat) (args:list expr)
  (pending:list (list expr))
  : Lemma (match modulus_search_acc fuel spent args pending with
           | None -> fuel < modulus_search_bound args pending
           | Some (result, work) ->
             result == modulus_search_result args pending /\
             work == spent + modulus_search_bound args pending /\ work <= spent + fuel)
          (decreases fuel) =
  if fuel > 0 then
    match args with
    | [] ->
      (match pending with
       | [] -> ()
       | next :: rest -> lemma_modulus_search_acc (fuel - 1) (spent + 1) next rest)
    | a :: rest ->
      lemma_modulus_of_metered fuel a;
      match modulus_of_metered fuel a with
      | None -> ()
      | Some (Some _, _) -> ()
      | Some (None, work) ->
        match a with
        | App _ children ->
          lemma_modulus_search_acc (fuel - work) (spent + work) children (rest :: pending);
          (match FF.find_modulus_args children with Some _ -> () | None -> ())
        | _ -> lemma_modulus_search_acc (fuel - work) (spent + work) rest pending

let find_modulus_bound (e:expr) : GTot pos = modulus_search_bound [e] []
let find_modulus_args_bound (args:list expr) : GTot pos = modulus_search_bound args []
let find_modulus_metered (fuel:nat) (e:expr) : Tot (option (option int & nat)) =
  modulus_search_acc fuel 0 [e] []
let find_modulus_args_metered (fuel:nat) (args:list expr) : Tot (option (option int & nat)) =
  modulus_search_acc fuel 0 args []

let lemma_find_modulus_metered (fuel:nat) (e:expr)
  : Lemma (match find_modulus_metered fuel e with
           | None -> fuel < find_modulus_bound e
           | Some (result, work) ->
             result == FF.find_modulus e /\ work == find_modulus_bound e /\ work <= fuel) =
  lemma_modulus_search_acc fuel 0 [e] []

let lemma_find_modulus_args_metered (fuel:nat) (args:list expr)
  : Lemma (match find_modulus_args_metered fuel args with
           | None -> fuel < find_modulus_args_bound args
           | Some (result, work) ->
             result == FF.find_modulus_args args /\
             work == find_modulus_args_bound args /\ work <= fuel) =
  lemma_modulus_search_acc fuel 0 args []

let count_at_most_bound (#a:Type) (limit:int) (xs:list a) : GTot pos =
  if limit < 0 then 1
  else 1 + (if L.length xs <= limit then L.length xs else limit)

let rec count_acc (#a:Type) (fuel limit count spent:nat) (xs:list a)
  : Tot (option (option nat & nat)) (decreases xs) =
  if fuel <= 0 then None
  else match xs with
    | [] -> Some (Some count, spent + 1)
    | _ :: rest ->
      if limit = 0 then Some (None, spent + 1)
      else count_acc (fuel - 1) (limit - 1) (count + 1) (spent + 1) rest

let rec lemma_count_acc (#a:Type) (fuel limit count spent:nat) (xs:list a)
  : Lemma (match count_acc fuel limit count spent xs with
           | None -> fuel < count_at_most_bound limit xs
           | Some (result, work) ->
             result == (if L.length xs <= limit then Some (count + L.length xs) else None) /\
             work == spent + count_at_most_bound limit xs /\ work <= spent + fuel)
          (decreases xs) =
  if fuel > 0 then
    match xs with
    | [] -> ()
    | _ :: rest ->
      if limit > 0 then lemma_count_acc (fuel - 1) (limit - 1) (count + 1) (spent + 1) rest

let count_at_most_metered (#a:Type) (fuel:nat) (limit:int) (xs:list a)
  : Tot (option (option nat & nat)) =
  if fuel <= 0 then None
  else if limit < 0 then Some (None, 1)
  else count_acc fuel limit 0 0 xs

let lemma_count_at_most_metered (#a:Type) (fuel:nat) (limit:int) (xs:list a)
  : Lemma (match count_at_most_metered fuel limit xs with
           | None -> fuel < count_at_most_bound limit xs
           | Some (result, work) ->
             result == (if L.length xs <= limit then Some (L.length xs) else None) /\
             work == count_at_most_bound limit xs /\ work <= fuel) =
  if fuel > 0 && limit >= 0 then lemma_count_acc fuel limit 0 0 xs

#push-options "--fuel 4 --ifuel 2"
let rec lemma_sort_eq_structural (a b:sort)
  : Lemma (sort_eq a b == (a = b)) (decreases a) =
  match a, b with
  | ArraySort ds r, ArraySort es s ->
    lemma_sort_list_eq_structural ds es;
    lemma_sort_eq_structural r s
  | SortApp _ ds, SortApp _ es -> lemma_sort_list_eq_structural ds es
  | _, _ -> ()

and lemma_sort_list_eq_structural (xs ys:list sort)
  : Lemma (sort_list_eq xs ys == (xs = ys)) (decreases xs) =
  match xs, ys with
  | a :: rest, b :: tail ->
    lemma_sort_eq_structural a b;
    lemma_sort_list_eq_structural rest tail
  | _, _ -> ()

let rec sort_comparison_weight (s:sort) : GTot pos (decreases s) =
  match s with
  | BaseSort _ -> 1
  | SortApp _ args -> 2 + sort_comparison_arguments_weight args
  | ArraySort ds r -> 3 + sort_comparison_arguments_weight ds + sort_comparison_weight r

and sort_comparison_arguments_weight (xs:list sort) : GTot nat (decreases xs) =
  match xs with
  | [] -> 0
  | s :: rest -> 1 + sort_comparison_weight s + sort_comparison_arguments_weight rest

let rec sort_comparison_pending_weight (pending:list (list sort & list sort))
  : GTot nat (decreases pending) =
  match pending with
  | [] -> 0
  | (xs, _) :: rest ->
    1 + sort_comparison_arguments_weight xs + sort_comparison_pending_weight rest

let rec sort_comparison_result (xs ys:list sort) (pending:list (list sort & list sort))
  : GTot bool (decreases pending) =
  sort_list_eq xs ys &&
    (match pending with
     | [] -> true
     | (next, other) :: rest -> sort_comparison_result next other rest)

let rec sort_comparison_bound (xs ys:list sort) (pending:list (list sort & list sort))
  : GTot pos
    (decreases (1 + sort_comparison_arguments_weight xs + sort_comparison_pending_weight pending)) =
  match xs, ys with
  | [], [] ->
    (match pending with
     | [] -> 1
     | (next, other) :: rest -> 1 + sort_comparison_bound next other rest)
  | a :: rest, b :: tail ->
    (match a, b with
     | BaseSort n, BaseSort m ->
       if n = m then 1 + sort_comparison_bound rest tail pending else 1
     | SortApp k ds, SortApp j es ->
       if k = j then 1 + sort_comparison_bound ds es ((rest, tail) :: pending) else 1
     | ArraySort ds r, ArraySort es s ->
       1 + sort_comparison_bound ds es (([r], [s]) :: (rest, tail) :: pending)
     | _, _ -> 1)
  | _, _ -> 1

let rec sort_comparison_acc (fuel spent:nat) (xs ys:list sort)
  (pending:list (list sort & list sort))
  : Tot (option (bool & nat)) (decreases fuel) =
  if fuel <= 0 then None
  else match xs, ys with
    | [], [] ->
      (match pending with
       | [] -> Some (true, spent + 1)
       | (next, other) :: rest -> sort_comparison_acc (fuel - 1) (spent + 1) next other rest)
    | a :: rest, b :: tail ->
      (match a, b with
       | BaseSort n, BaseSort m ->
         if n = m then sort_comparison_acc (fuel - 1) (spent + 1) rest tail pending
         else Some (false, spent + 1)
       | SortApp k ds, SortApp j es ->
         if k = j then sort_comparison_acc (fuel - 1) (spent + 1) ds es ((rest, tail) :: pending)
         else Some (false, spent + 1)
       | ArraySort ds r, ArraySort es s ->
         sort_comparison_acc (fuel - 1) (spent + 1) ds es (([r], [s]) :: (rest, tail) :: pending)
       | _, _ -> Some (false, spent + 1))
    | _, _ -> Some (false, spent + 1)

let rec lemma_sort_comparison_acc (fuel spent:nat) (xs ys:list sort)
  (pending:list (list sort & list sort))
  : Lemma (match sort_comparison_acc fuel spent xs ys pending with
           | None -> fuel < sort_comparison_bound xs ys pending
           | Some (result, work) ->
             result == sort_comparison_result xs ys pending /\
             work == spent + sort_comparison_bound xs ys pending /\ work <= spent + fuel)
          (decreases fuel) =
  if fuel > 0 then
    match xs, ys with
    | [], [] ->
      (match pending with
       | [] -> ()
       | (next, other) :: rest -> lemma_sort_comparison_acc (fuel - 1) (spent + 1) next other rest)
    | a :: rest, b :: tail ->
      (match a, b with
       | BaseSort n, BaseSort m ->
         if n = m then lemma_sort_comparison_acc (fuel - 1) (spent + 1) rest tail pending
       | SortApp k ds, SortApp j es ->
         if k = j then lemma_sort_comparison_acc (fuel - 1) (spent + 1) ds es ((rest, tail) :: pending)
       | ArraySort ds r, ArraySort es s ->
         lemma_sort_comparison_acc (fuel - 1) (spent + 1) ds es (([r], [s]) :: (rest, tail) :: pending)
       | _, _ -> ())
    | _, _ -> ()

let sort_eq_bound (a b:sort) : GTot pos = sort_comparison_bound [a] [b] []
let sort_list_eq_bound (xs ys:list sort) : GTot pos = sort_comparison_bound xs ys []
let sort_eq_metered (fuel:nat) (a b:sort) : Tot (option (bool & nat)) =
  sort_comparison_acc fuel 0 [a] [b] []
let sort_list_eq_metered (fuel:nat) (xs ys:list sort) : Tot (option (bool & nat)) =
  sort_comparison_acc fuel 0 xs ys []

let lemma_sort_eq_metered (fuel:nat) (a b:sort)
  : Lemma (match sort_eq_metered fuel a b with
           | None -> fuel < sort_eq_bound a b
           | Some (result, work) ->
             result == sort_eq a b /\ result == (a = b) /\
             work == sort_eq_bound a b /\ work <= fuel) =
  lemma_sort_eq_structural a b;
  lemma_sort_comparison_acc fuel 0 [a] [b] []

let lemma_sort_list_eq_metered (fuel:nat) (xs ys:list sort)
  : Lemma (match sort_list_eq_metered fuel xs ys with
           | None -> fuel < sort_list_eq_bound xs ys
           | Some (result, work) ->
             result == sort_list_eq xs ys /\ result == (xs = ys) /\
             work == sort_list_eq_bound xs ys /\ work <= fuel) =
  lemma_sort_list_eq_structural xs ys;
  lemma_sort_comparison_acc fuel 0 xs ys []
#pop-options

#push-options "--fuel 4 --ifuel 2"
let rec int_list_eq_bound (xs ys:list int) : GTot pos (decreases xs) =
  match xs, ys with
  | a :: rest, b :: tail -> if a = b then 1 + int_list_eq_bound rest tail else 1
  | _, _ -> 1

let rec int_list_eq_acc (fuel spent:nat) (xs ys:list int)
  : Tot (option (bool & nat)) (decreases fuel) =
  if fuel <= 0 then None
  else match xs, ys with
    | [], [] -> Some (true, spent + 1)
    | a :: rest, b :: tail ->
      if a = b then int_list_eq_acc (fuel - 1) (spent + 1) rest tail
      else Some (false, spent + 1)
    | _, _ -> Some (false, spent + 1)

let rec lemma_int_list_eq_acc (fuel spent:nat) (xs ys:list int)
  : Lemma (match int_list_eq_acc fuel spent xs ys with
           | None -> fuel < int_list_eq_bound xs ys
           | Some (result, work) ->
             result == (xs = ys) /\
             work == spent + int_list_eq_bound xs ys /\ work <= spent + fuel)
          (decreases fuel) =
  if fuel > 0 then
    match xs, ys with
    | a :: rest, b :: tail ->
      if a = b then lemma_int_list_eq_acc (fuel - 1) (spent + 1) rest tail
    | _, _ -> ()

let int_list_eq_metered (fuel:nat) (xs ys:list int) : Tot (option (bool & nat)) =
  int_list_eq_acc fuel 0 xs ys

let lemma_int_list_eq_metered (fuel:nat) (xs ys:list int)
  : Lemma (match int_list_eq_metered fuel xs ys with
           | None -> fuel < int_list_eq_bound xs ys
           | Some (result, work) ->
             result == (xs = ys) /\
             work == int_list_eq_bound xs ys /\ work <= fuel) =
  lemma_int_list_eq_acc fuel 0 xs ys

let decl_eq_bound (f g:func_decl) : GTot pos =
  if f.decl_name <> g.decl_name then 1
  else
    let domain = 1 + sort_list_eq_bound f.domain g.domain in
    if f.domain <> g.domain then domain
    else
      let ranged = domain + sort_eq_bound f.range g.range in
      if f.range <> g.range then ranged
      else
        let metadata = ranged + 1 in
        if f.interp <> g.interp then metadata
        else metadata + int_list_eq_bound f.int_params g.int_params

let decl_eq_metered (fuel:nat) (f g:func_decl) : Tot (option (bool & nat)) =
  if fuel <= 0 then None
  else if f.decl_name <> g.decl_name then Some (false, 1)
  else
    let _ = lemma_sort_list_eq_metered (fuel - 1) f.domain g.domain in
    match sort_list_eq_metered (fuel - 1) f.domain g.domain with
    | None -> None
    | Some (false, work) -> Some (false, 1 + work)
    | Some (true, work) ->
      let domain = 1 + work in
      let _ = lemma_sort_eq_metered (fuel - domain) f.range g.range in
      match sort_eq_metered (fuel - domain) f.range g.range with
      | None -> None
      | Some (false, extra) -> Some (false, domain + extra)
      | Some (true, extra) ->
        let ranged = domain + extra in
        if fuel <= ranged then None
        else
          let metadata = ranged + 1 in
          if f.interp <> g.interp then Some (false, metadata)
          else
            let _ = lemma_int_list_eq_metered (fuel - metadata) f.int_params g.int_params in
            match int_list_eq_metered (fuel - metadata) f.int_params g.int_params with
            | None -> None
            | Some (result, params_work) -> Some (result, metadata + params_work)

let lemma_decl_eq_metered (fuel:nat) (f g:func_decl)
  : Lemma (match decl_eq_metered fuel f g with
           | None -> fuel < decl_eq_bound f g
           | Some (result, work) ->
             result == (f = g) /\ work == decl_eq_bound f g /\ work <= fuel) =
  if fuel > 0 && f.decl_name = g.decl_name then (
    lemma_sort_list_eq_metered (fuel - 1) f.domain g.domain;
    match sort_list_eq_metered (fuel - 1) f.domain g.domain with
    | Some (true, work) ->
      let domain = 1 + work in
      lemma_sort_eq_metered (fuel - domain) f.range g.range;
      (match sort_eq_metered (fuel - domain) f.range g.range with
       | Some (true, extra) ->
         let ranged = domain + extra in
         if fuel > ranged && f.interp = g.interp then
           lemma_int_list_eq_metered (fuel - ranged - 1) f.int_params g.int_params
       | _ -> ())
    | _ -> ())
#pop-options

let allocate_bound (st:FF.encoding) : GTot pos =
  1 + count_at_most_bound (FF.max_variables - 1) st.FF.terms +
    (if L.length st.FF.terms < FF.max_variables then L.length st.FF.terms + 1 else 0)

let allocate_metered (fuel:nat) (st:FF.encoding) (t:expr)
  : Tot (option (option FF.encoding & nat)) =
  if fuel <= 0 then None
  else
    let _ = lemma_count_at_most_metered (fuel - 1) (FF.max_variables - 1) st.FF.terms in
    match count_at_most_metered (fuel - 1) (FF.max_variables - 1) st.FF.terms with
    | None -> None
    | Some (None, work) -> Some (None, 1 + work)
    | Some (Some n, work) ->
      let spent = 1 + work in
      let copying = n + 1 in
      if fuel - spent < copying then None
      else Some (Some { st with FF.terms = L.append st.FF.terms [t] }, spent + copying)

let lemma_allocate_metered (fuel:nat) (st:FF.encoding) (t:expr)
  : Lemma (match allocate_metered fuel st t with
           | None -> fuel < allocate_bound st
           | Some (result, work) ->
             result == FF.allocate st t /\
             work == allocate_bound st /\ work <= fuel) =
  if fuel > 0 then
    lemma_count_at_most_metered (fuel - 1) (FF.max_variables - 1) st.FF.terms

let rec boolean_sorts_bound (domain:list sort) : GTot pos (decreases domain) =
  match domain with
  | [] -> 1
  | s :: rest -> 1 + (if s = bool_sort then boolean_sorts_bound rest else 0)

let rec boolean_sorts_acc (fuel spent:nat) (domain:list sort)
  : Tot (option (bool & nat)) (decreases domain) =
  if fuel <= 0 then None
  else match domain with
    | [] -> Some (true, spent + 1)
    | s :: rest ->
      if s = bool_sort then boolean_sorts_acc (fuel - 1) (spent + 1) rest
      else Some (false, spent + 1)

let rec lemma_boolean_sorts_acc (fuel spent:nat) (domain:list sort)
  : Lemma (match boolean_sorts_acc fuel spent domain with
           | None -> fuel < boolean_sorts_bound domain
           | Some (result, work) ->
             result == Canonical.boolean_sorts domain /\
             work == spent + boolean_sorts_bound domain /\ work <= spent + fuel)
          (decreases domain) =
  if fuel > 0 then
    match domain with
    | [] -> ()
    | s :: rest ->
      if s = bool_sort then lemma_boolean_sorts_acc (fuel - 1) (spent + 1) rest

let boolean_sorts_metered (fuel:nat) (domain:list sort) : Tot (option (bool & nat)) =
  boolean_sorts_acc fuel 0 domain

let lemma_boolean_sorts_metered (fuel:nat) (domain:list sort)
  : Lemma (match boolean_sorts_metered fuel domain with
           | None -> fuel < boolean_sorts_bound domain
           | Some (result, work) ->
             result == Canonical.boolean_sorts domain /\
             work == boolean_sorts_bound domain /\ work <= fuel) =
  lemma_boolean_sorts_acc fuel 0 domain

let canonical_or_bound (f:func_decl) : GTot pos =
  1 + (if f.decl_name = "or" && f.interp = Some Z3OperatorTags.op_or
       then boolean_sorts_bound f.domain else 0)

let canonical_or_metered (fuel:nat) (f:func_decl) : Tot (option (bool & nat)) =
  if fuel <= 0 then None
  else if f.decl_name <> "or" || f.interp <> Some Z3OperatorTags.op_or
  then Some (false, 1)
  else
    let _ = lemma_boolean_sorts_metered (fuel - 1) f.domain in
    match boolean_sorts_metered (fuel - 1) f.domain with
    | None -> None
    | Some (valid, work) ->
      Some (valid && f.range = bool_sort && f.int_params = [], 1 + work)

let lemma_canonical_or_metered (fuel:nat) (f:func_decl)
  : Lemma (match canonical_or_metered fuel f with
           | None -> fuel < canonical_or_bound f
           | Some (result, work) ->
             result == Canonical.canonical_or f /\
             work == canonical_or_bound f /\ work <= fuel) =
  if fuel > 0 && f.decl_name = "or" && f.interp = Some Z3OperatorTags.op_or
  then lemma_boolean_sorts_metered (fuel - 1) f.domain

let clause_literals_bound (e:expr) : GTot pos =
  match e with
  | App f _ -> canonical_or_bound f
  | _ -> 1

let clause_literals_metered (fuel:nat) (e:expr) : Tot (option (list expr & nat)) =
  if fuel <= 0 then None
  else match e with
    | App f args ->
      let _ = lemma_canonical_or_metered fuel f in
      (match canonical_or_metered fuel f with
       | None -> None
       | Some (valid, work) -> Some ((if valid then args else [e]), work))
    | _ -> Some ([e], 1)

let lemma_clause_literals_metered (fuel:nat) (e:expr)
  : Lemma (match clause_literals_metered fuel e with
           | None -> fuel < clause_literals_bound e
           | Some (result, work) ->
             result == FF.clause_literals e /\
             work == clause_literals_bound e /\ work <= fuel) =
  match e with
  | App f _ -> lemma_canonical_or_metered fuel f
  | _ -> ()

let check_for_prime_bound (p:int{E.is_prime p}) (c:FF.certificate) (e:expr) : GTot nat =
  let n = L.length c.FF.pac_premises in
  let premises = 1 + count_at_most_bound FF.max_premises c.FF.pac_premises in
  if n = 0 || n > FF.max_premises then premises
  else
    let header = premises + count_at_most_bound FF.max_nodes c.FF.pac_nodes in
    if L.length c.FF.pac_nodes > FF.max_nodes then header
    else
      let discovery = header + find_modulus_args_bound c.FF.pac_premises in
      if FF.find_modulus_args c.FF.pac_premises <> Some p then discovery
      else
        let admission = discovery + support_tree_bound n (-1) c.FF.pac_support in
        match FF.support_tree n (-1) IX.Empty c.FF.pac_support with
        | None -> admission
        | Some sup ->
          match Witness.bind p 0 FF.empty_encoding c.FF.pac_premises with
          | None -> admission
          | Some st ->
            let indexed = admission + 1 + L.length st.FF.equations +
              index_equations_bound (L.length st.FF.equations - 1) st.FF.equations in
            let setup = indexed + 1 + L.length st.FF.terms + clause_literals_bound e in
            let eqs = FF.index_equations IX.Empty
                        (L.length st.FF.equations - 1) st.FF.equations in
            let lits = FF.clause_literals e in
            let nvars = L.length st.FF.terms in
            let replay = Metered.replay_bound p nvars eqs sup lits Pac.initial c.FF.pac_nodes in
            (match Pac.replay_nodes p nvars eqs sup lits Pac.initial c.FF.pac_nodes with
             | None -> setup + replay
             | Some r -> setup + replay + Metered.finalize_bound r c.FF.pac_root c.FF.pac_support)

let check_for_prime_metered (fuel:nat) (p:int{E.is_prime p}) (c:FF.certificate) (e:expr)
  : Tot (option (bool & nat)) =
  if fuel <= 0 then None
  else
    let _ = lemma_count_at_most_metered (fuel - 1) FF.max_premises c.FF.pac_premises in
    match count_at_most_metered (fuel - 1) FF.max_premises c.FF.pac_premises with
    | None -> None
    | Some (None, work) -> Some (false, 1 + work)
    | Some (Some n, work) ->
      let premises = 1 + work in
      if n = 0 then Some (false, premises)
      else (
        let _ = lemma_count_at_most_metered (fuel - premises) FF.max_nodes c.FF.pac_nodes in
        match count_at_most_metered (fuel - premises) FF.max_nodes c.FF.pac_nodes with
        | None -> None
        | Some (None, extra) -> Some (false, premises + extra)
        | Some (Some _, extra) ->
          let header = premises + extra in
          let _ = lemma_find_modulus_args_metered (fuel - header) c.FF.pac_premises in
          match find_modulus_args_metered (fuel - header) c.FF.pac_premises with
          | None -> None
          | Some (modulus, discovery_work) ->
            let admission = header + discovery_work in
            if modulus <> Some p then Some (false, admission)
            else (
              let _ = lemma_support_tree_metered (fuel - admission) n (-1) IX.Empty c.FF.pac_support in
              match support_tree_metered (fuel - admission) n (-1) IX.Empty c.FF.pac_support with
              | None -> None
              | Some (None, work) -> Some (false, admission + work)
              | Some (Some sup, support_work) ->
                let spent = admission + support_work in
                match Witness.bind p 0 FF.empty_encoding c.FF.pac_premises with
                | None -> Some (false, spent)
                | Some st ->
                  let available = fuel - spent in
                  let _ = lemma_count_at_most_metered available available st.FF.equations in
                  (match count_at_most_metered available available st.FF.equations with
                   | Some (Some count, count_work) ->
                     let counted = spent + count_work in
                     let k = count - 1 in
                     let _ = lemma_index_equations_metered (fuel - counted) IX.Empty k st.FF.equations in
                     (match index_equations_metered (fuel - counted) IX.Empty k st.FF.equations with
                      | None -> None
                      | Some (eqs, index_work) ->
                        let indexed = counted + index_work in
                        let available = fuel - indexed in
                        let _ = lemma_count_at_most_metered available available st.FF.terms in
                        match count_at_most_metered available available st.FF.terms with
                        | Some (Some nvars, term_work) ->
                          let counted_terms = indexed + term_work in
                          let _ = lemma_clause_literals_metered (fuel - counted_terms) e in
                          (match clause_literals_metered (fuel - counted_terms) e with
                           | None -> None
                           | Some (lits, clause_work) ->
                             let setup = counted_terms + clause_work in
                             Metered.lemma_replay_nodes_metered (fuel - setup) p nvars eqs sup lits
                               Pac.initial c.FF.pac_nodes;
                             match Metered.replay_nodes_metered (fuel - setup) p nvars eqs sup lits
                                     Pac.initial c.FF.pac_nodes with
                             | None -> None
                             | Some (None, work) -> Some (false, setup + work)
                             | Some (Some r, work) ->
                               match Metered.finalize_metered (fuel - setup - work) r c.FF.pac_root c.FF.pac_support with
                               | None -> None
                               | Some (result, extra) -> Some (result, setup + work + extra))
                        | _ -> None)
                   | _ -> None)))

let lemma_check_for_prime_metered (fuel:nat) (p:int{E.is_prime p})
  (c:FF.certificate) (e:expr)
  : Lemma (match check_for_prime_metered fuel p c e with
           | None -> fuel < check_for_prime_bound p c e
           | Some (result, work) ->
             result == check_for_prime p c e /\ 0 < work /\
             work <= fuel /\ work <= check_for_prime_bound p c e) =
  if fuel > 0 then (
    lemma_count_at_most_metered (fuel - 1) FF.max_premises c.FF.pac_premises;
    match count_at_most_metered (fuel - 1) FF.max_premises c.FF.pac_premises with
    | Some (Some n, work) ->
      if n > 0 then (
        let premises = 1 + work in
        lemma_count_at_most_metered (fuel - premises) FF.max_nodes c.FF.pac_nodes;
        match count_at_most_metered (fuel - premises) FF.max_nodes c.FF.pac_nodes with
        | Some (Some _, extra) ->
          let header = premises + extra in
          lemma_find_modulus_args_metered (fuel - header) c.FF.pac_premises;
          (match find_modulus_args_metered (fuel - header) c.FF.pac_premises with
           | Some (modulus, discovery_work) ->
             if modulus = Some p then (
               let admission = header + discovery_work in
               lemma_support_tree_metered (fuel - admission) n (-1) IX.Empty c.FF.pac_support;
               match support_tree_metered (fuel - admission) n (-1) IX.Empty c.FF.pac_support with
               | Some (Some sup, support_work) ->
                 (match Witness.bind p 0 FF.empty_encoding c.FF.pac_premises with
                  | Some st ->
                    let spent = admission + support_work in
                    let available = fuel - spent in
                    lemma_count_at_most_metered available available st.FF.equations;
                    (match count_at_most_metered available available st.FF.equations with
                     | Some (Some count, count_work) ->
                       let counted = spent + count_work in
                       let k = count - 1 in
                       lemma_index_equations_metered (fuel - counted) IX.Empty k st.FF.equations;
                       (match index_equations_metered (fuel - counted) IX.Empty k st.FF.equations with
                        | Some (eqs, index_work) ->
                          let indexed = counted + index_work in
                          let available = fuel - indexed in
                          lemma_count_at_most_metered available available st.FF.terms;
                          (match count_at_most_metered available available st.FF.terms with
                           | Some (Some nvars, term_work) ->
                             let counted_terms = indexed + term_work in
                             lemma_clause_literals_metered (fuel - counted_terms) e;
                             (match clause_literals_metered (fuel - counted_terms) e with
                              | Some (lits, clause_work) ->
                                let setup = counted_terms + clause_work in
                                Metered.lemma_replay_nodes_metered (fuel - setup) p nvars eqs sup lits
                                  Pac.initial c.FF.pac_nodes;
                                (match Metered.replay_nodes_metered (fuel - setup) p nvars eqs sup lits
                                         Pac.initial c.FF.pac_nodes with
                                 | Some (Some r, work) ->
                                   Metered.lemma_finalize_metered (fuel - setup - work) r c.FF.pac_root c.FF.pac_support
                                 | _ -> ())
                              | None -> ())
                           | _ -> ())
                        | None -> ())
                     | _ -> ())
                  | None -> ())
               | _ -> ())
           | None -> ())
        | _ -> ())
    | _ -> ())

let lemma_check_for_prime_metered_sound (#base:sort -> Type0) (schema:S.checked_schema)
  (fuel:nat) (p:int{E.is_prime p}) (m:FF.model base schema p)
  (c:FF.certificate) (e:expr) (work:nat)
  : Lemma (requires D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\
                    check_for_prime_metered fuel p c e == Some (true, work))
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e) =
  lemma_check_for_prime_metered fuel p c e;
  lemma_check_for_prime_sound schema p m c e

let rec lemma_support_tree_count (n:nat) (previous:int{-1 <= previous /\ previous < n})
  (tree:IX.index_tree bool) (support:list int)
  : Lemma (requires Some? (FF.support_tree n previous tree support))
          (ensures L.length support <= n - previous - 1)
          (decreases support) =
  match support with
  | [] -> ()
  | k :: rest ->
    lemma_support_tree_count n k (IX.index_put tree k true) rest

let lemma_support_length_rejected (c:FF.certificate) (e:expr)
  (evidence:option (int & list int))
  : Lemma (requires L.length c.FF.pac_support > L.length c.FF.pac_premises)
          (ensures check_with_evidence c e evidence == false) =
  let n = L.length c.FF.pac_premises in
  if Some? (FF.support_tree n (-1) IX.Empty c.FF.pac_support) then
    lemma_support_tree_count n (-1) IX.Empty c.FF.pac_support

let header_bound (c:FF.certificate) : GTot pos =
  let n = L.length c.FF.pac_premises in
  count_at_most_bound FF.max_premises c.FF.pac_premises +
    (if 0 < n && n <= FF.max_premises
     then count_at_most_bound FF.max_nodes c.FF.pac_nodes +
       (if L.length c.FF.pac_nodes <= FF.max_nodes
        then count_at_most_bound n c.FF.pac_support else 0)
     else 0)

let admit_header_metered (fuel:nat) (c:FF.certificate)
  : Tot (option (option (nat & nat) & nat)) =
  lemma_count_at_most_metered fuel FF.max_premises c.FF.pac_premises;
  match count_at_most_metered fuel FF.max_premises c.FF.pac_premises with
  | None -> None
  | Some (None, work) -> Some (None, work)
  | Some (Some n, work) ->
    if n = 0 then Some (None, work)
    else
      let _ = lemma_count_at_most_metered (fuel - work) FF.max_nodes c.FF.pac_nodes in
      match count_at_most_metered (fuel - work) FF.max_nodes c.FF.pac_nodes with
      | None -> None
      | Some (None, extra) -> Some (None, work + extra)
      | Some (Some nodes, extra) ->
        match count_at_most_metered (fuel - work - extra) n c.FF.pac_support with
        | None -> None
        | Some (None, support_work) -> Some (None, work + extra + support_work)
        | Some (Some _, support_work) -> Some (Some (n, nodes), work + extra + support_work)

let lemma_admit_header_metered (fuel:nat) (c:FF.certificate)
  : Lemma (match admit_header_metered fuel c with
           | None -> fuel < header_bound c
           | Some (result, work) ->
             result == (if 0 < L.length c.FF.pac_premises &&
                           L.length c.FF.pac_premises <= FF.max_premises &&
                           L.length c.FF.pac_nodes <= FF.max_nodes &&
                           L.length c.FF.pac_support <= L.length c.FF.pac_premises
                        then Some (L.length c.FF.pac_premises, L.length c.FF.pac_nodes)
                        else None) /\
             work == header_bound c /\ work <= fuel) =
  lemma_count_at_most_metered fuel FF.max_premises c.FF.pac_premises;
  match count_at_most_metered fuel FF.max_premises c.FF.pac_premises with
  | Some (Some n, work) ->
    if n > 0 then (
      lemma_count_at_most_metered (fuel - work) FF.max_nodes c.FF.pac_nodes;
      match count_at_most_metered (fuel - work) FF.max_nodes c.FF.pac_nodes with
      | Some (Some _, extra) ->
        lemma_count_at_most_metered (fuel - work - extra) n c.FF.pac_support
      | _ -> ())
  | _ -> ()

let check_with_evidence_bound (c:FF.certificate) (e:expr)
  (evidence:option (int & list int)) : GTot nat =
  let n = L.length c.FF.pac_premises in
  let admission = 1 + header_bound c in
  if n = 0 || n > FF.max_premises || L.length c.FF.pac_nodes > FF.max_nodes ||
     L.length c.FF.pac_support > n then admission
  else
    let setup = admission + find_modulus_args_bound c.FF.pac_premises in
    match FF.find_modulus_args c.FF.pac_premises with
    | Some p ->
      if Witness.prime_with_evidence p evidence
      then setup + check_for_prime_bound p c e
      else setup
    | None -> setup

let check_with_evidence_metered (fuel:nat) (c:FF.certificate) (e:expr)
  (evidence:option (int & list int)) : Tot (option (bool & nat)) =
  if fuel <= 0 then None
  else
    let _ = lemma_admit_header_metered (fuel - 1) c in
    match admit_header_metered (fuel - 1) c with
    | None -> None
    | Some (None, work) -> Some (false, 1 + work)
    | Some (Some _, work) ->
      let admission = 1 + work in
      let _ = lemma_find_modulus_args_metered (fuel - admission) c.FF.pac_premises in
      match find_modulus_args_metered (fuel - admission) c.FF.pac_premises with
      | None -> None
      | Some (modulus, discovery_work) ->
        let spent = admission + discovery_work in
        match modulus with
        | Some p ->
          if Witness.prime_with_evidence p evidence then
            (match check_for_prime_metered (fuel - spent) p c e with
             | None -> None
             | Some (result, extra) -> Some (result, spent + extra))
          else Some (false, spent)
        | None -> Some (false, spent)

let lemma_check_with_evidence_metered (fuel:nat) (c:FF.certificate) (e:expr)
  (evidence:option (int & list int))
  : Lemma (match check_with_evidence_metered fuel c e evidence with
           | None -> fuel < check_with_evidence_bound c e evidence
           | Some (result, work) ->
             result == check_with_evidence c e evidence /\ 0 < work /\
             work <= fuel /\ work <= check_with_evidence_bound c e evidence) =
  if L.length c.FF.pac_support > L.length c.FF.pac_premises then
    lemma_support_length_rejected c e evidence;
  if fuel > 0 then (
    lemma_admit_header_metered (fuel - 1) c;
    match admit_header_metered (fuel - 1) c with
    | Some (Some _, work) ->
      (let admission = 1 + work in
       lemma_find_modulus_args_metered (fuel - admission) c.FF.pac_premises;
       match find_modulus_args_metered (fuel - admission) c.FF.pac_premises with
       | Some (Some p, discovery_work) ->
         if Witness.prime_with_evidence p evidence then
           lemma_check_for_prime_metered (fuel - admission - discovery_work) p c e
       | _ -> ())
    | _ -> ())

let lemma_check_with_evidence_metered_sound (#base:sort -> Type0) (schema:S.checked_schema)
  (fuel:nat) (p:pos) (m:FF.model base schema p) (c:FF.certificate) (e:expr)
  (evidence:option (int & list int)) (work:nat)
  : Lemma (requires FF.find_modulus_args c.FF.pac_premises == Some p /\
                    D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\
                    check_with_evidence_metered fuel c e evidence == Some (true, work))
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e) =
  lemma_check_with_evidence_metered fuel c e evidence;
  lemma_check_with_evidence_sound schema p m c e evidence
