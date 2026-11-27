module Z3IndependentFiniteFieldWitness

open Z3AstTheory
module E = FStar.Math.Euclid
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module D = Z3ExprScope
module FF = Z3SortedFiniteField
module SS = Z3SortedSemantics
module L = FStar.List.Tot
module PT = Z3ProofTheory
module IX = Z3ProofIndex
module Prime = Z3IndependentFiniteFieldPrime
module Evidence = Z3IndependentPrimeEvidence

let rec complementary_in (l:expr) (lits:list expr) : Tot bool (decreases lits) =
  match lits with
  | [] -> false
  | x :: rest ->
    PT.is_not x = Some l ||
    (PT.is_not l = Some x && get_sort x = bool_sort) ||
    complementary_in l rest

let witness_polynomial (k:nat) (qa qb:FF.poly) : FF.poly =
  FF.padd (FF.pmul [([k], 1)] (FF.padd qa (FF.pscale (-1) qb))) [([], -1)]

let premise_equation (p:int) (k:nat) (l a b:expr) (st:FF.encoding)
  (positive:bool) : option FF.encoding =
  if positive then FF.premise_equation p k l a b st true
  else
    match FF.term_poly p st.FF.terms a, FF.term_poly p st.FF.terms b, FF.allocate st l with
    | Some qa, Some qb, Some st1 ->
      FF.push st1 (witness_polynomial (L.length st.FF.terms) qa qb, FF.Premise k l)
    | _, _, _ -> None

let rec bind (p:int) (k:nat) (st:FF.encoding) (ps:list expr)
  : Tot (option FF.encoding) (decreases ps) =
  match ps with
  | [] -> Some st
  | l :: rest ->
    (match FF.premise_parts p l with
     | None -> None
     | Some (positive, a, b) ->
       (match FF.visit p st a with
        | None -> None
        | Some st1 ->
          (match FF.visit p st1 b with
           | None -> None
           | Some st2 ->
             (match premise_equation p k l a b st2 positive with
              | None -> None
              | Some st3 -> bind p (k + 1) st3 rest))))

let step (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:FF.replay) (n:FF.pac_node)
  : option FF.replay =
  match n with
  | FF.PacInput j ->
    if j < 0 then None
    else
      (match IX.index_get eqs j with
       | Some (q, FF.Premise k l) ->
         if IX.index_get sup k = Some true && complementary_in l lits &&
            r.FF.work + FF.poly_size q <= FF.max_work
         then FF.record p r (FF.poly_size q) q (IX.index_put r.FF.used k true)
         else None
       | _ -> FF.step p nvars eqs sup lits r n)
  | _ -> FF.step p nvars eqs sup lits r n

let rec replay_nodes (p:pos) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:FF.replay) (ns:list FF.pac_node)
  : Tot (option FF.replay) (decreases ns) =
  match ns with
  | [] -> Some r
  | n :: rest ->
    (match step p nvars eqs sup lits r n with
     | None -> None
     | Some r' -> replay_nodes p nvars eqs sup lits r' rest)

let prime_with_evidence (p:int) (evidence:option (int & list int))
  : Tot (ok:bool{ok ==> E.is_prime p}) =
  Prime.small_prime p ||
  (match evidence with
   | None -> false
   | Some (a, factors) -> Evidence.check p a factors)

let check_for_prime (p:int{E.is_prime p}) (c:FF.certificate) (e:expr) : bool =
  let n = L.length c.FF.pac_premises in
  if n = 0 || n > FF.max_premises || L.length c.FF.pac_nodes > FF.max_nodes ||
     FF.find_modulus_args c.FF.pac_premises <> Some p then false
  else
    (match bind p 0 FF.empty_encoding c.FF.pac_premises,
           FF.support_tree n (-1) IX.Empty c.FF.pac_support with
     | Some st, Some sup ->
       let eqs = FF.index_equations IX.Empty
                   (L.length st.FF.equations - 1) st.FF.equations in
       (match replay_nodes p (L.length st.FF.terms) eqs sup
                (FF.clause_literals e) FF.initial_replay c.FF.pac_nodes with
        | Some r -> FF.unit_root r c.FF.pac_root && FF.all_used r.FF.used c.FF.pac_support
        | None -> false)
     | _, _ -> false)

let check_with_evidence (c:FF.certificate) (e:expr)
  (evidence:option (int & list int)) : bool =
  let n = L.length c.FF.pac_premises in
  if n = 0 || n > FF.max_premises || L.length c.FF.pac_nodes > FF.max_nodes then false
  else match FF.find_modulus_args c.FF.pac_premises with
    | Some p -> if prime_with_evidence p evidence then check_for_prime p c e else false
    | None -> false

let check (c:FF.certificate) (e:expr) : bool =
  check_with_evidence c e None

val lemma_complementary_in (#base:sort -> Type0) (schema:S.checked_schema)
  (p:pos) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (l:expr) (lits:list expr)
  : Lemma (requires D.scoped_args [] lits /\
                    FF.none_true schema p m rho lits /\ complementary_in l lits)
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] rho l)

val slot (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (e:expr{D.scoped [] e}) : GTot int

val lemma_field_slot (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (e:expr{D.scoped [] e /\ get_sort e == FF.ff_sort p})
  : Lemma (slot schema p m rho e == FF.residue schema p m rho e)

val lemma_witness_slot (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (l:expr{D.scoped [] l}) (a:expr{D.scoped [] a}) (b:expr{D.scoped [] b})
  : Lemma (requires FF.premise_parts p l == Some (false, a, b) /\
                    FF.truth_at schema p m [] rho l)
          (ensures (slot schema p m rho l *
                    (FF.residue schema p m rho a - FF.residue schema p m rho b) - 1) % p == 0)

val valuation (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl:list expr{D.scoped_args [] tbl}) : GTot (nat -> int)

val lemma_valuation_field (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl:list expr{D.scoped_args [] tbl}) (k:nat)
  : Lemma (requires k < L.length tbl /\ get_sort (L.index tbl k) == FF.ff_sort p)
          (ensures valuation schema p m rho tbl k == FF.valuation schema p m rho tbl k)

val lemma_valuation_witness (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl:list expr{D.scoped_args [] tbl}) (k:nat)
  (a:expr{D.scoped [] a}) (b:expr{D.scoped [] b})
  : Lemma (requires k < L.length tbl /\
                    FF.premise_parts p (L.index tbl k) == Some (false, a, b) /\
                    FF.truth_at schema p m [] rho (L.index tbl k))
          (ensures (valuation schema p m rho tbl k *
                    (FF.residue schema p m rho a - FF.residue schema p m rho b) - 1) % p == 0)

val lemma_term_poly (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl final:list expr) (t:expr) (q:FF.poly)
  : Lemma (requires D.scoped [] t /\ get_sort t == FF.ff_sort p /\
                    D.scoped_args [] final /\ FF.prefix tbl final /\
                    FF.term_poly p tbl t == Some q)
          (ensures FF.peval (valuation schema p m rho final) q % p ==
                   FF.residue schema p m rho t)

val lemma_term_polys (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl final:list expr) (args:list expr) (qs:list FF.poly)
  : Lemma (requires D.scoped_args [] args /\ FF.args_have_sort p args /\
                    D.scoped_args [] final /\ FF.prefix tbl final /\
                    FF.term_polys p tbl args == Some qs)
          (ensures FF.match_list (valuation schema p m rho final) p qs
                   (FF.expressions_residues schema p m rho args))

val lemma_definition (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl final:list expr) (f:func_decl) (args:list expr)
  (op:decl_kind) (qs:list FF.poly) (fq:FF.poly)
  : Lemma (requires D.scoped [] (App f args) /\
                    FF.operation_at f args == Some (p, op) /\
                    D.scoped_args [] final /\ FF.prefix tbl final /\
                    L.length tbl < L.length final /\
                    L.index final (L.length tbl) == App f args /\
                    FF.term_polys p tbl args == Some qs /\ FF.combine op qs == Some fq)
          (ensures FF.peval (valuation schema p m rho final)
                    (FF.definition (L.length tbl) fq) % p == 0)

val lemma_visit (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (st:FF.encoding) (t:expr) (st':FF.encoding) (final:list expr)
  : Lemma (requires D.scoped_args [] st.FF.terms /\ D.scoped [] t /\
                    D.scoped_args [] final /\ FF.visit p st t == Some st' /\
                    FF.prefix st'.FF.terms final)
          (ensures FF.prefix st.FF.terms st'.FF.terms /\
                   (FF.eqs_ok schema p m rho (valuation schema p m rho final) st.FF.equations ==>
                    FF.eqs_ok schema p m rho (valuation schema p m rho final) st'.FF.equations))

val lemma_visit_args (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (st:FF.encoding) (args:list expr) (st':FF.encoding) (final:list expr)
  : Lemma (requires D.scoped_args [] st.FF.terms /\ D.scoped_args [] args /\
                    D.scoped_args [] final /\ FF.visit_args p st args == Some st' /\
                    FF.prefix st'.FF.terms final)
          (ensures FF.prefix st.FF.terms st'.FF.terms /\
                   (FF.eqs_ok schema p m rho (valuation schema p m rho final) st.FF.equations ==>
                    FF.eqs_ok schema p m rho (valuation schema p m rho final) st'.FF.equations))

val lemma_witness_polynomial (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (tbl:list expr) (final:list expr{D.scoped_args [] final}) (k:nat)
  (a b:expr) (qa qb:FF.poly)
  : Lemma (requires FF.prefix tbl final /\ k < L.length final /\
                    FF.premise_parts p (L.index final k) == Some (false, a, b) /\
                    FF.truth_at schema p m [] rho (L.index final k) /\
                    FF.term_poly p tbl a == Some qa /\ FF.term_poly p tbl b == Some qb)
          (ensures FF.peval (valuation schema p m rho final) (witness_polynomial k qa qb) % p == 0)

val lemma_premise_equation (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (k:nat) (l a b:expr) (st st':FF.encoding) (positive:bool) (final:list expr)
  : Lemma (requires D.scoped_args [] st.FF.terms /\ D.scoped_args [] final /\
                    D.scoped [] l /\ FF.premise_parts p l == Some (positive, a, b) /\
                    premise_equation p k l a b st positive == Some st' /\
                    FF.prefix st'.FF.terms final)
          (ensures FF.prefix st.FF.terms st'.FF.terms /\
                   (FF.eqs_ok schema p m rho (valuation schema p m rho final) st.FF.equations ==>
                    FF.eqs_ok schema p m rho (valuation schema p m rho final) st'.FF.equations))

val lemma_bind_scoped (p:int) (k:nat) (st:FF.encoding) (ps:list expr) (st':FF.encoding)
  : Lemma (requires D.scoped_args [] st.FF.terms /\ D.scoped_args [] ps /\
                    bind p k st ps == Some st')
          (ensures D.scoped_args [] st'.FF.terms)

val lemma_bind (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p)
  (rho:V.environment base (S.signature schema) [])
  (k:nat) (st:FF.encoding) (ps:list expr) (st':FF.encoding) (final:list expr)
  : Lemma (requires D.scoped_args [] st.FF.terms /\ D.scoped_args [] ps /\
                    D.scoped_args [] final /\ bind p k st ps == Some st' /\
                    FF.prefix st'.FF.terms final)
          (ensures FF.prefix st.FF.terms st'.FF.terms /\
                   (FF.eqs_ok schema p m rho (valuation schema p m rho final) st.FF.equations ==>
                    FF.eqs_ok schema p m rho (valuation schema p m rho final) st'.FF.equations))

val lemma_step (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
  (m:FF.model base schema p) (rho:V.environment base (S.signature schema) [])
  (v:nat -> int) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:FF.replay) (n:FF.pac_node) (r':FF.replay)
  : Lemma (requires D.scoped_args [] lits /\ FF.tree_ok schema p m rho v eqs /\
                    FF.values_ok schema p m rho v lits r.FF.values /\
                    step p nvars eqs sup lits r n == Some r')
          (ensures FF.values_ok schema p m rho v lits r'.FF.values)

val lemma_replay_nodes (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
  (m:FF.model base schema p) (rho:V.environment base (S.signature schema) [])
  (v:nat -> int) (nvars:nat) (eqs:IX.index_tree FF.equation)
  (sup:IX.index_tree bool) (lits:list expr) (r:FF.replay) (ns:list FF.pac_node) (r':FF.replay)
  : Lemma (requires D.scoped_args [] lits /\ FF.tree_ok schema p m rho v eqs /\
                    FF.values_ok schema p m rho v lits r.FF.values /\
                    replay_nodes p nvars eqs sup lits r ns == Some r')
          (ensures FF.values_ok schema p m rho v lits r'.FF.values)

val lemma_check_for_prime_sound (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p) (c:FF.certificate) (e:expr)
  : Lemma (requires D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\ check_for_prime p c e)
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e)

val lemma_check_with_evidence_sound (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
  (m:FF.model base schema p) (c:FF.certificate) (e:expr)
  (evidence:option (int & list int))
  : Lemma (requires FF.find_modulus_args c.FF.pac_premises == Some p /\
                    D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\ check_with_evidence c e evidence)
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e)

val lemma_check_sound (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
  (m:FF.model base schema p) (c:FF.certificate) (e:expr)
  : Lemma (requires FF.find_modulus_args c.FF.pac_premises == Some p /\
                    D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\ check c e)
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e)
