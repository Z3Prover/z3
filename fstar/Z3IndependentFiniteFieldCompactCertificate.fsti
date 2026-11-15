module Z3IndependentFiniteFieldCompactCertificate

open Z3AstTheory
module E = FStar.Math.Euclid
module S = Z3DatatypeSignature
module D = Z3ExprScope
module FF = Z3SortedFiniteField
module Canonical = Z3CanonicalOps
module IX = Z3ProofIndex
module SS = Z3SortedSemantics

val check_for_prime (p:int{E.is_prime p}) (c:FF.certificate) (e:expr) : Tot bool
val check_with_evidence (c:FF.certificate) (e:expr)
  (evidence:option (int & list int)) : Tot bool
val check (c:FF.certificate) (e:expr) : Tot bool
val lemma_check_for_prime_sound (#base:sort -> Type0) (schema:S.checked_schema)
  (p:int{E.is_prime p}) (m:FF.model base schema p) (c:FF.certificate) (e:expr)
  : Lemma (requires D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\ check_for_prime p c e)
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e)
val lemma_check_with_evidence_sound (#base:sort -> Type0) (schema:S.checked_schema)
  (p:pos) (m:FF.model base schema p) (c:FF.certificate) (e:expr)
  (evidence:option (int & list int))
  : Lemma (requires FF.find_modulus_args c.FF.pac_premises == Some p /\
                    D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\ check_with_evidence c e evidence)
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e)
val lemma_check_sound (#base:sort -> Type0) (schema:S.checked_schema)
  (p:pos) (m:FF.model base schema p) (c:FF.certificate) (e:expr)
  : Lemma (requires FF.find_modulus_args c.FF.pac_premises == Some p /\
                    D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\ check c e)
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e)

val support_tree_bound (n previous:int) (support:list int) : GTot pos
val support_tree_metered (fuel:nat) (n previous:int)
  (tree:IX.index_tree bool) (support:list int)
  : Tot (option (option (IX.index_tree bool) & nat))
val lemma_support_tree_metered (fuel:nat) (n previous:int)
  (tree:IX.index_tree bool) (support:list int)
  : Lemma (match support_tree_metered fuel n previous tree support with
           | None -> fuel < support_tree_bound n previous support
           | Some (result, work) ->
             result == FF.support_tree n previous tree support /\
             work == support_tree_bound n previous support /\ work <= fuel)

val index_equations_bound (k:int) (equations:list FF.equation) : GTot pos
val index_equations_metered (fuel:nat) (tree:IX.index_tree FF.equation)
  (k:int) (equations:list FF.equation)
  : Tot (option (IX.index_tree FF.equation & nat))
val lemma_index_equations_metered (fuel:nat) (tree:IX.index_tree FF.equation)
  (k:int) (equations:list FF.equation)
  : Lemma (match index_equations_metered fuel tree k equations with
           | None -> fuel < index_equations_bound k equations
           | Some (result, work) ->
             result == FF.index_equations tree k equations /\
             work == index_equations_bound k equations /\ work <= fuel)

val domain_arity_bound (p:int) (domain:list sort) : GTot pos
val domain_arity_metered (fuel:nat) (p:int) (domain:list sort)
  : Tot (option (option nat & nat))
val lemma_domain_arity_metered (fuel:nat) (p:int) (domain:list sort)
  : Lemma (match domain_arity_metered fuel p domain with
           | None -> fuel < domain_arity_bound p domain
           | Some (result, work) ->
             result == (if sort_list_eq domain (FF.repeat_sort p (FStar.List.Tot.length domain))
                        then Some (FStar.List.Tot.length domain) else None) /\
             work == domain_arity_bound p domain /\ work <= fuel)
val operation_of_bound (f:func_decl) : GTot pos
val operation_of_metered (fuel:nat) (f:func_decl)
  : Tot (option (option (int & decl_kind) & nat))
val lemma_operation_of_metered (fuel:nat) (f:func_decl)
  : Lemma (match operation_of_metered fuel f with
           | None -> fuel < operation_of_bound f
           | Some (result, work) ->
             result == FF.operation_of f /\ work == operation_of_bound f /\ work <= fuel)

val arguments_match_bound (p:int) (domain:list sort) (args:list expr) : GTot pos
val arguments_match_metered (fuel:nat) (p:int) (domain:list sort) (args:list expr)
  : Tot (option (bool & nat))
val lemma_arguments_match_metered (fuel:nat) (p:int) (domain:list sort) (args:list expr)
  : Lemma (match arguments_match_metered fuel p domain args with
           | None -> fuel < arguments_match_bound p domain args
           | Some (result, work) ->
             result == (FF.args_have_sort p args &&
                        FStar.List.Tot.length args = FStar.List.Tot.length domain) /\
             work == arguments_match_bound p domain args /\ work <= fuel)
val operation_at_bound (f:func_decl) (args:list expr) : GTot pos
val operation_at_metered (fuel:nat) (f:func_decl) (args:list expr)
  : Tot (option (option (int & decl_kind) & nat))
val lemma_operation_at_metered (fuel:nat) (f:func_decl) (args:list expr)
  : Lemma (match operation_at_metered fuel f args with
           | None -> fuel < operation_at_bound f args
           | Some (result, work) ->
             result == FF.operation_at f args /\ work == operation_at_bound f args /\ work <= fuel)

val modulus_of_bound (e:expr) : GTot pos
val modulus_of_metered (fuel:nat) (e:expr) : Tot (option (option int & nat))
val lemma_modulus_of_metered (fuel:nat) (e:expr)
  : Lemma (match modulus_of_metered fuel e with
           | None -> fuel < modulus_of_bound e
           | Some (result, work) ->
             result == FF.modulus_of e /\ work == modulus_of_bound e /\ work <= fuel)

val find_modulus_bound (e:expr) : GTot pos
val find_modulus_args_bound (args:list expr) : GTot pos
val find_modulus_metered (fuel:nat) (e:expr) : Tot (option (option int & nat))
val find_modulus_args_metered (fuel:nat) (args:list expr) : Tot (option (option int & nat))
val lemma_find_modulus_metered (fuel:nat) (e:expr)
  : Lemma (match find_modulus_metered fuel e with
           | None -> fuel < find_modulus_bound e
           | Some (result, work) ->
             result == FF.find_modulus e /\ work == find_modulus_bound e /\ work <= fuel)
val lemma_find_modulus_args_metered (fuel:nat) (args:list expr)
  : Lemma (match find_modulus_args_metered fuel args with
           | None -> fuel < find_modulus_args_bound args
           | Some (result, work) ->
             result == FF.find_modulus_args args /\
             work == find_modulus_args_bound args /\ work <= fuel)

val count_at_most_bound (#a:Type) (limit:int) (xs:list a) : GTot pos
val count_at_most_metered (#a:Type) (fuel:nat) (limit:int) (xs:list a)
  : Tot (option (option nat & nat))
val lemma_count_at_most_metered (#a:Type) (fuel:nat) (limit:int) (xs:list a)
  : Lemma (match count_at_most_metered fuel limit xs with
           | None -> fuel < count_at_most_bound limit xs
           | Some (result, work) ->
             result == (if FStar.List.Tot.length xs <= limit
                        then Some (FStar.List.Tot.length xs) else None) /\
             work == count_at_most_bound limit xs /\ work <= fuel)

val lemma_sort_eq_structural (a b:sort)
  : Lemma (sort_eq a b == (a = b))
val lemma_sort_list_eq_structural (xs ys:list sort)
  : Lemma (sort_list_eq xs ys == (xs = ys))
val sort_eq_bound (a b:sort) : GTot pos
val sort_list_eq_bound (xs ys:list sort) : GTot pos
val sort_eq_metered (fuel:nat) (a b:sort) : Tot (option (bool & nat))
val sort_list_eq_metered (fuel:nat) (xs ys:list sort) : Tot (option (bool & nat))
val lemma_sort_eq_metered (fuel:nat) (a b:sort)
  : Lemma (match sort_eq_metered fuel a b with
           | None -> fuel < sort_eq_bound a b
           | Some (result, work) ->
             result == sort_eq a b /\ result == (a = b) /\
             work == sort_eq_bound a b /\ work <= fuel)
val lemma_sort_list_eq_metered (fuel:nat) (xs ys:list sort)
  : Lemma (match sort_list_eq_metered fuel xs ys with
           | None -> fuel < sort_list_eq_bound xs ys
           | Some (result, work) ->
             result == sort_list_eq xs ys /\ result == (xs = ys) /\
             work == sort_list_eq_bound xs ys /\ work <= fuel)

val int_list_eq_bound (xs ys:list int) : GTot pos
val int_list_eq_metered (fuel:nat) (xs ys:list int) : Tot (option (bool & nat))
val lemma_int_list_eq_metered (fuel:nat) (xs ys:list int)
  : Lemma (match int_list_eq_metered fuel xs ys with
           | None -> fuel < int_list_eq_bound xs ys
           | Some (result, work) ->
             result == (xs = ys) /\
             work == int_list_eq_bound xs ys /\ work <= fuel)
val decl_eq_bound (f g:func_decl) : GTot pos
val decl_eq_metered (fuel:nat) (f g:func_decl) : Tot (option (bool & nat))
val lemma_decl_eq_metered (fuel:nat) (f g:func_decl)
  : Lemma (match decl_eq_metered fuel f g with
           | None -> fuel < decl_eq_bound f g
           | Some (result, work) ->
             result == (f = g) /\ work == decl_eq_bound f g /\ work <= fuel)

val allocate_bound (st:FF.encoding) : GTot pos
val allocate_metered (fuel:nat) (st:FF.encoding) (t:expr)
  : Tot (option (option FF.encoding & nat))
val lemma_allocate_metered (fuel:nat) (st:FF.encoding) (t:expr)
  : Lemma (match allocate_metered fuel st t with
           | None -> fuel < allocate_bound st
           | Some (result, work) ->
             result == FF.allocate st t /\
             work == allocate_bound st /\ work <= fuel)

val boolean_sorts_bound (domain:list sort) : GTot pos
val boolean_sorts_metered (fuel:nat) (domain:list sort) : Tot (option (bool & nat))
val lemma_boolean_sorts_metered (fuel:nat) (domain:list sort)
  : Lemma (match boolean_sorts_metered fuel domain with
           | None -> fuel < boolean_sorts_bound domain
           | Some (result, work) ->
             result == Canonical.boolean_sorts domain /\
             work == boolean_sorts_bound domain /\ work <= fuel)
val canonical_or_bound (f:func_decl) : GTot pos
val canonical_or_metered (fuel:nat) (f:func_decl) : Tot (option (bool & nat))
val lemma_canonical_or_metered (fuel:nat) (f:func_decl)
  : Lemma (match canonical_or_metered fuel f with
           | None -> fuel < canonical_or_bound f
           | Some (result, work) ->
             result == Canonical.canonical_or f /\
             work == canonical_or_bound f /\ work <= fuel)
val clause_literals_bound (e:expr) : GTot pos
val clause_literals_metered (fuel:nat) (e:expr) : Tot (option (list expr & nat))
val lemma_clause_literals_metered (fuel:nat) (e:expr)
  : Lemma (match clause_literals_metered fuel e with
           | None -> fuel < clause_literals_bound e
           | Some (result, work) ->
             result == FF.clause_literals e /\
             work == clause_literals_bound e /\ work <= fuel)

val check_for_prime_bound (p:int{E.is_prime p}) (c:FF.certificate) (e:expr) : GTot nat
val check_for_prime_metered (fuel:nat) (p:int{E.is_prime p}) (c:FF.certificate) (e:expr)
  : Tot (option (bool & nat))
val lemma_check_for_prime_metered (fuel:nat) (p:int{E.is_prime p})
  (c:FF.certificate) (e:expr)
  : Lemma (match check_for_prime_metered fuel p c e with
           | None -> fuel < check_for_prime_bound p c e
           | Some (result, work) ->
             result == check_for_prime p c e /\ 0 < work /\
             work <= fuel /\ work <= check_for_prime_bound p c e)
val lemma_check_for_prime_metered_sound (#base:sort -> Type0) (schema:S.checked_schema)
  (fuel:nat) (p:int{E.is_prime p}) (m:FF.model base schema p)
  (c:FF.certificate) (e:expr) (work:nat)
  : Lemma (requires D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\
                    check_for_prime_metered fuel p c e == Some (true, work))
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e)

val lemma_support_length_rejected (c:FF.certificate) (e:expr)
  (evidence:option (int & list int))
  : Lemma (requires FStar.List.Tot.length c.FF.pac_support >
                    FStar.List.Tot.length c.FF.pac_premises)
          (ensures check_with_evidence c e evidence == false)
val header_bound (c:FF.certificate) : GTot pos
val admit_header_metered (fuel:nat) (c:FF.certificate)
  : Tot (option (option (nat & nat) & nat))
val lemma_admit_header_metered (fuel:nat) (c:FF.certificate)
  : Lemma (match admit_header_metered fuel c with
           | None -> fuel < header_bound c
           | Some (result, work) ->
             result == (if 0 < FStar.List.Tot.length c.FF.pac_premises &&
                           FStar.List.Tot.length c.FF.pac_premises <= FF.max_premises &&
                           FStar.List.Tot.length c.FF.pac_nodes <= FF.max_nodes &&
                           FStar.List.Tot.length c.FF.pac_support <=
                             FStar.List.Tot.length c.FF.pac_premises
                        then Some (FStar.List.Tot.length c.FF.pac_premises,
                                   FStar.List.Tot.length c.FF.pac_nodes)
                        else None) /\
             work == header_bound c /\ work <= fuel)

val check_with_evidence_bound (c:FF.certificate) (e:expr)
  (evidence:option (int & list int)) : GTot nat
val check_with_evidence_metered (fuel:nat) (c:FF.certificate) (e:expr)
  (evidence:option (int & list int)) : Tot (option (bool & nat))
val lemma_check_with_evidence_metered (fuel:nat) (c:FF.certificate) (e:expr)
  (evidence:option (int & list int))
  : Lemma (match check_with_evidence_metered fuel c e evidence with
           | None -> fuel < check_with_evidence_bound c e evidence
           | Some (result, work) ->
             result == check_with_evidence c e evidence /\ 0 < work /\
             work <= fuel /\ work <= check_with_evidence_bound c e evidence)
val lemma_check_with_evidence_metered_sound (#base:sort -> Type0) (schema:S.checked_schema)
  (fuel:nat) (p:pos) (m:FF.model base schema p) (c:FF.certificate) (e:expr)
  (evidence:option (int & list int)) (work:nat)
  : Lemma (requires FF.find_modulus_args c.FF.pac_premises == Some p /\
                    D.scoped_args [] c.FF.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\
                    check_with_evidence_metered fuel c e evidence == Some (true, work))
          (ensures SS.truth_at schema m.FF.booleans m.FF.scalar_model
                    (FF.override schema p m) [] (SS.empty_environment (S.signature schema)) e)
