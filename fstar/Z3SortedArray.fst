module Z3SortedArray

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3ExprScope
module A = Z3ArraySyntax
module F = Z3ArrayTheory
module FE = FStar.FunctionalExtensionality
module ID = FStar.IndefiniteDescription
module BR = Z3SortedBooleanRewrite

noeq type algebra (index element array:Type0) = {
  read: array -> index -> GTot element;
  write: array -> index -> element -> GTot array;
  constant: element -> GTot array;
  difference: array -> array -> GTot index;
  extensional: a:array -> b:array ->
    Lemma (requires (forall (k:index). read a k == read b k)) (ensures a == b);
  laws: u:unit{
    (forall (a:array) (j k:index) (v:element).
      read (write a j v) k == (if ID.strong_excluded_middle (j == k) then v else read a k)) /\
    (forall (v:element) (k:index). read (constant v) k == v) /\
    (forall (a b:array).
      a == b \/ ~(read a (difference a b) == read b (difference a b)))};
}

let functional (#index #element:Type0) (fallback:index)
  : GTot (algebra index element (F.semantic_arr index element)) =
  let read = F.semantic_select #index #element in
  let write = F.semantic_store #index #element in
  let constant = fun (v:element) -> F.semantic_lambda (fun (_:index) -> v) in
  let difference (a b:F.semantic_arr index element)
    : GTot (k:index{a == b \/ ~(read a k == read b k)}) =
    if ID.strong_excluded_middle (a == b) then fallback
    else (
      F.lemma_semantic_extensionality a b;
      ID.indefinite_description_ghost index (fun k -> ~(read a k == read b k))) in
  let extensional (a b:F.semantic_arr index element)
    : Lemma (requires (forall (k:index). read a k == read b k)) (ensures a == b) =
    F.lemma_semantic_extensionality a b in
  let witness (a b:F.semantic_arr index element)
    : Lemma (a == b \/ ~(read a (difference a b) == read b (difference a b))) = () in
  FStar.Classical.forall_intro_2 witness;
  { read = read; write = write; constant = constant; difference = difference;
    extensional = extensional; laws = () }

let lemma_overwrite (#index #element #array:Type0) (m:algebra index element array)
                    (a:array) (k:index) (v w:element)
  : Lemma (m.write (m.write a k v) k w == m.write a k w) =
  let pointwise (j:index)
    : Lemma (m.read (m.write (m.write a k v) k w) j == m.read (m.write a k w) j) = () in
  FStar.Classical.forall_intro pointwise;
  m.extensional (m.write (m.write a k v) k w) (m.write a k w)

let lemma_read_other (#index #element #array:Type0) (m:algebra index element array)
                     (a:array) (j k:index) (v:element)
  : Lemma (requires ~(j == k)) (ensures m.read (m.write a j v) k == m.read a k) = ()

let lemma_redundant (#index #element #array:Type0) (m:algebra index element array)
                    (a:array) (k:index)
  : Lemma (m.write a k (m.read a k) == a) =
  let pointwise (j:index)
    : Lemma (m.read (m.write a k (m.read a k)) j == m.read a j) = () in
  FStar.Classical.forall_intro pointwise;
  m.extensional (m.write a k (m.read a k)) a

type array_value (base:sort -> Type0) (sigma:V.signature) (index element:sort) =
  V.value base sigma (ArraySort [index] element)

let select_decl (index element:sort) : func_decl = {
  decl_name = "select"; domain = [ArraySort [index] element; index]; range = element;
  interp = Some Z3OperatorTags.op_select; int_params = [];
}

let store_decl (index element:sort) : func_decl = {
  decl_name = "store"; domain = [ArraySort [index] element; index; element];
  range = ArraySort [index] element;
  interp = Some Z3OperatorTags.op_store; int_params = [];
}

let ext_decl (index element:sort) : func_decl = {
  decl_name = "array-ext"; domain = [ArraySort [index] element; ArraySort [index] element];
  range = index;
  interp = Some Z3OperatorTags.op_array_ext; int_params = [];
}

noeq type family (base:sort -> Type0) (sigma:V.signature) = {
  supports: sort -> sort -> bool;
  arrays: index:sort -> element:sort{supports index element} ->
    GTot (algebra (V.value base sigma index) (V.value base sigma element)
      (array_value base sigma index element));
}

let rec supported (#base:sort -> Type0) (#sigma:V.signature)
                  (m:family base sigma) (e:expr) : Tot bool (decreases e) =
  (match get_sort e with ArraySort [index] element -> m.supports index element | _ -> true) &&
  (match e with
   | App _ args -> supported_args m args
   | Quantifier _ _ _ body -> supported m body
   | _ -> true)

and supported_args (#base:sort -> Type0) (#sigma:V.signature)
                   (m:family base sigma) (args:list expr) : Tot bool (decreases args) =
  match args with [] -> true | a :: rest -> supported m a && supported_args m rest

let model (#base:sort -> Type0) (s:S.checked_schema)
          (bc:S.boolean_carrier base) (core:T.scalar_model base)
          (other:V.interpretation base (S.signature s))
          (m:family base (S.signature s)) : prop =
  (forall (index:sort) (element:sort{m.supports index element})
          (a:array_value base (S.signature s) index element)
          (k:V.value base (S.signature s) index).
    T.application s bc core other (select_decl index element) [a; k] ==
    (m.arrays index element).read a k) /\
  (forall (index:sort) (element:sort{m.supports index element})
          (a:array_value base (S.signature s) index element)
          (k:V.value base (S.signature s) index) (v:V.value base (S.signature s) element).
    T.application s bc core other (store_decl index element) [a; k; v] ==
    (m.arrays index element).write a k v) /\
  (forall (index:sort) (element:sort{m.supports index element})
          (a b:array_value base (S.signature s) index element).
    T.application s bc core other (ext_decl index element) [a; b] ==
    (m.arrays index element).difference a b)

let lemma_scope_select (scope:list sort) (index element:sort) (a k:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope k /\
                    get_sort a == ArraySort [index] element /\ get_sort k == index)
          (ensures D.scoped scope (App (select_decl index element) [a; k]))
          [SMTPat (D.scoped scope (App (select_decl index element) [a; k]))] =
  V.lemma_sort_eq (get_sort a) (ArraySort [index] element);
  V.lemma_sort_eq (get_sort k) index;
  assert (D.scoped_args scope [k]);
  assert (D.scoped_args scope [a; k]);
  assert (sorts_match [k] [index]);
  assert (sorts_match [a; k] [ArraySort [index] element; index])

let lemma_scope_store (scope:list sort) (index element:sort) (a k v:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope k /\ D.scoped scope v /\
                    get_sort a == ArraySort [index] element /\
                    get_sort k == index /\ get_sort v == element)
          (ensures D.scoped scope (App (store_decl index element) [a; k; v]))
          [SMTPat (D.scoped scope (App (store_decl index element) [a; k; v]))] =
  V.lemma_sort_eq (get_sort a) (ArraySort [index] element);
  V.lemma_sort_eq (get_sort k) index;
  V.lemma_sort_eq (get_sort v) element;
  assert (D.scoped_args scope [v]);
  assert (D.scoped_args scope [k; v]);
  assert (D.scoped_args scope [a; k; v]);
  assert (sorts_match [v] [element]);
  assert (sorts_match [k; v] [index; element]);
  assert (sorts_match [a; k; v] [ArraySort [index] element; index; element])

let lemma_select (#base:sort -> Type0) (s:S.checked_schema)
                 (bc:S.boolean_carrier base) (core:T.scalar_model base)
                 (other:V.interpretation base (S.signature s))
                 (m:family base (S.signature s))
                 (scope:list sort) (rho:V.environment base (S.signature s) scope)
                 (index:sort) (element:sort{m.supports index element})
                 (a:expr{D.scoped scope a /\ get_sort a == ArraySort [index] element})
                 (k:expr{D.scoped scope k /\ get_sort k == index})
  : Lemma (requires model s bc core other m)
          (ensures T.evaluate_at s bc core other scope rho
                     (App (select_decl index element) [a; k]) ==
                   (m.arrays index element).read
                     (T.evaluate_at s bc core other scope rho a)
                     (T.evaluate_at s bc core other scope rho k)) =
  let av = T.evaluate_at s bc core other scope rho a in
  let kv = T.evaluate_at s bc core other scope rho k in
  assert (T.evaluate_arguments_at s bc core other scope rho [k] [index] == [kv]);
  assert (T.evaluate_arguments_at s bc core other scope rho [a; k]
            [ArraySort [index] element; index] == [av; kv]);
  assert (T.application s bc core other (select_decl index element) [av; kv] ==
          (m.arrays index element).read av kv)

let lemma_store (#base:sort -> Type0) (s:S.checked_schema)
                (bc:S.boolean_carrier base) (core:T.scalar_model base)
                (other:V.interpretation base (S.signature s))
                (m:family base (S.signature s))
                (scope:list sort) (rho:V.environment base (S.signature s) scope)
                (index:sort) (element:sort{m.supports index element})
                (a:expr{D.scoped scope a /\ get_sort a == ArraySort [index] element})
                (k:expr{D.scoped scope k /\ get_sort k == index})
                (v:expr{D.scoped scope v /\ get_sort v == element})
  : Lemma (requires model s bc core other m)
          (ensures T.evaluate_at s bc core other scope rho
                     (App (store_decl index element) [a; k; v]) ==
                   (m.arrays index element).write
                     (T.evaluate_at s bc core other scope rho a)
                     (T.evaluate_at s bc core other scope rho k)
                     (T.evaluate_at s bc core other scope rho v)) =
  let av = T.evaluate_at s bc core other scope rho a in
  let kv = T.evaluate_at s bc core other scope rho k in
  let vv = T.evaluate_at s bc core other scope rho v in
  assert (T.evaluate_arguments_at s bc core other scope rho [v] [element] == [vv]);
  assert (T.evaluate_arguments_at s bc core other scope rho [k; v] [index; element] == [kv; vv]);
  assert (T.evaluate_arguments_at s bc core other scope rho [a; k; v]
            [ArraySort [index] element; index; element] == [av; kv; vv]);
  assert (T.application s bc core other (store_decl index element) [av; kv; vv] ==
          (m.arrays index element).write av kv vv)

let lemma_read_over_write_same (#base:sort -> Type0) (s:S.checked_schema)
                              (bc:S.boolean_carrier base) (core:T.scalar_model base)
                              (other:V.interpretation base (S.signature s))
                              (m:family base (S.signature s))
                              (scope:list sort) (rho:V.environment base (S.signature s) scope)
                              (a b:expr)
  : Lemma (requires model s bc core other m /\ D.scoped scope a /\ D.scoped scope b /\
                    supported m a /\ supported m b /\ A.read_over_write_same a b)
          (ensures T.evaluate_at s bc core other scope rho a ==
                   T.evaluate_at s bc core other scope rho b) =
  match a with
  | App _ [App _ [base; k; v]; j] ->
    (match get_sort base with
     | ArraySort [index] element ->
       lemma_store s bc core other m scope rho index element base k v;
       lemma_select s bc core other m scope rho index element
         (App (store_decl index element) [base; k; v]) j
     | _ -> ())
  | _ -> ()

let lemma_ite_shape (#base:sort -> Type0) (#sigma:V.signature)
                    (m:family base sigma) (scope:list sort) (c t u:expr)
  : Lemma (requires D.scoped scope c /\ D.scoped scope t /\ D.scoped scope u /\
                    supported m c /\ supported m t /\ supported m u /\
                    get_sort c == bool_sort /\ get_sort t == get_sort u)
          (ensures
            (let e = App (A.term_ite_decl (get_sort t)) [c; t; u] in
             D.scoped scope e /\ supported m e /\ get_sort e == get_sort t)) =
  V.lemma_sort_eq (get_sort c) bool_sort;
  V.lemma_sort_eq (get_sort t) (get_sort t);
  V.lemma_sort_eq (get_sort u) (get_sort t);
  assert (D.scoped_args scope [u]);
  assert (D.scoped_args scope [t; u]);
  assert (D.scoped_args scope [c; t; u]);
  assert (sorts_match [u] [get_sort t]);
  assert (sorts_match [t; u] [get_sort t; get_sort t]);
  assert (sorts_match [c; t; u] [bool_sort; get_sort t; get_sort t])

let lemma_boolean_pair_shape (#base:sort -> Type0) (#sigma:V.signature)
                             (m:family base sigma) (scope:list sort)
                             (op:Z3BooleanRewriteSyntax.connective) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\
                    supported m a /\ supported m b /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort)
          (ensures
            (let e = App (Z3BooleanRewriteSyntax.connective_decl op [a; b]) [a; b] in
             D.scoped scope e /\ supported m e /\ get_sort e == bool_sort)) =
  V.lemma_sort_eq (get_sort a) bool_sort;
  V.lemma_sort_eq (get_sort b) bool_sort;
  assert (D.scoped_args scope [b]);
  assert (D.scoped_args scope [a; b]);
  assert (sorts_match [b] [bool_sort]);
  assert (sorts_match [a; b] [bool_sort; bool_sort])

let lemma_read_over_write_other (#base:sort -> Type0) (s:S.checked_schema)
                               (bc:S.boolean_carrier base) (core:T.scalar_model base)
                               (other:V.interpretation base (S.signature s))
                               (m:family base (S.signature s))
                               (scope:list sort) (rho:V.environment base (S.signature s) scope)
                               (guard a b:expr)
  : Lemma (requires model s bc core other m /\
                    D.scoped scope guard /\ D.scoped scope a /\ D.scoped scope b /\
                    supported m a /\ supported m b /\ A.read_over_write_other guard a b)
          (ensures T.truth_at s bc core other scope rho guard \/
                   T.evaluate_at s bc core other scope rho a ==
                   T.evaluate_at s bc core other scope rho b) =
  match guard, a, b with
  | App _ [u; w], App _ [App wf [base; j; v]; k], App _ [base'; k'] ->
    let stored = App wf [base; j; v] in
    assert (A.equality_parts guard == Some (u, w));
    assert (A.select_parts a == Some (stored, k));
    assert (A.select_parts b == Some (base', k'));
    assert (A.store_parts stored == Some (base, j, v));
    A.lemma_other_indices guard a b u w stored k base' k' base j v;
    T.lemma_equality_at s bc core other scope rho u w;
    (match get_sort base with
     | ArraySort [index] element ->
       lemma_store s bc core other m scope rho index element base j v;
       lemma_select s bc core other m scope rho index element
         (App (store_decl index element) [base; j; v]) k;
       lemma_select s bc core other m scope rho index element base k;
       assert (A.same_indices u w j k);
       assert (guard == Z3ClauseSyntax.mk_eq_expr u w);
       assert (a == App (select_decl index element)
         [App (store_decl index element) [base; j; v]; k]);
       assert (b == App (select_decl index element) [base; k]);
       let jv = T.evaluate_at s bc core other scope rho j in
       let kv = T.evaluate_at s bc core other scope rho k in
       if ID.strong_excluded_middle (jv == kv) then
         assert (T.truth_at s bc core other scope rho guard)
       else
         lemma_read_other (m.arrays index element)
           (T.evaluate_at s bc core other scope rho base) jv kv
           (T.evaluate_at s bc core other scope rho v)
     | _ -> ())
  | _, _, _ -> ()

let lemma_ext (#base:sort -> Type0) (s:S.checked_schema)
              (bc:S.boolean_carrier base) (core:T.scalar_model base)
              (other:V.interpretation base (S.signature s))
              (m:family base (S.signature s))
              (scope:list sort) (rho:V.environment base (S.signature s) scope)
              (index:sort) (element:sort{m.supports index element})
              (e:expr{D.scoped scope e})
              (a:expr{D.scoped scope a /\ get_sort a == ArraySort [index] element})
              (b:expr{D.scoped scope b /\ get_sort b == ArraySort [index] element})
  : Lemma (requires model s bc core other m /\ e == App (ext_decl index element) [a; b])
          (ensures T.evaluate_at s bc core other scope rho e ==
                   (m.arrays index element).difference
                     (T.evaluate_at s bc core other scope rho a)
                     (T.evaluate_at s bc core other scope rho b)) =
  let av = T.evaluate_at s bc core other scope rho a in
  let bv = T.evaluate_at s bc core other scope rho b in
  assert (T.evaluate_arguments_at s bc core other scope rho [b]
            [ArraySort [index] element] == [bv]);
  assert (T.evaluate_arguments_at s bc core other scope rho [a; b]
            [ArraySort [index] element; ArraySort [index] element] == [av; bv]);
  assert (T.application s bc core other (ext_decl index element) [av; bv] ==
          (m.arrays index element).difference av bv)

let lemma_extensionality (#base:sort -> Type0) (s:S.checked_schema)
                         (bc:S.boolean_carrier base) (core:T.scalar_model base)
                         (other:V.interpretation base (S.signature s))
                         (m:family base (S.signature s))
                         (scope:list sort) (rho:V.environment base (S.signature s) scope)
                         (a b x y:expr)
  : Lemma (requires model s bc core other m /\
                    D.scoped scope a /\ D.scoped scope b /\
                    D.scoped scope x /\ D.scoped scope y /\
                    supported m x /\ supported m y /\ A.extensionality a b x y)
          (ensures T.evaluate_at s bc core other scope rho a ==
                   T.evaluate_at s bc core other scope rho b \/
                   ~(T.evaluate_at s bc core other scope rho x ==
                     T.evaluate_at s bc core other scope rho y)) =
  match x, y with
  | App _ [_; k], App _ [_; _] ->
    (match get_sort a, k with
     | ArraySort [index] element, App _ [u; v] ->
       lemma_select s bc core other m scope rho index element a k;
       lemma_select s bc core other m scope rho index element b k;
       lemma_ext s bc core other m scope rho index element k u v
     | _, _ -> ())
  | _, _ -> ()

let lemma_array_clause (#base:sort -> Type0) (s:S.checked_schema)
                       (bc:S.boolean_carrier base) (core:T.scalar_model base)
                       (other:V.interpretation base (S.signature s))
                       (m:family base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (p q:expr)
  : Lemma (requires model s bc core other m /\
                    D.scoped scope p /\ D.scoped scope q /\
                    supported m p /\ supported m q /\ A.array_clause p q)
          (ensures T.truth_at s bc core other scope rho p \/
                   T.truth_at s bc core other scope rho q) =
  match A.equality_parts p, A.equality_parts q with
  | _, Some (a, b) ->
    assert (q == Z3ClauseSyntax.mk_eq_expr a b);
    T.lemma_equality_at s bc core other scope rho a b;
    if A.read_over_write_other p a b then
      lemma_read_over_write_other s bc core other m scope rho p a b
    else lemma_read_over_write_other s bc core other m scope rho p b a
  | Some (a, b), None ->
    assert (p == Z3ClauseSyntax.mk_eq_expr a b);
    T.lemma_equality_at s bc core other scope rho a b;
    (match q with
     | App f [negated] ->
       (match A.equality_parts negated with
        | Some (x, y) ->
          assert (negated == Z3ClauseSyntax.mk_eq_expr x y);
          T.lemma_equality_at s bc core other scope rho x y;
          if A.extensionality a b x y then
            lemma_extensionality s bc core other m scope rho a b x y
          else lemma_extensionality s bc core other m scope rho b a x y;
          assert (q == Z3ClauseSyntax.mk_not_expr negated);
          BR.lemma_not_at s bc core other scope rho negated
        | None -> ())
     | _ -> ())
  | _, _ -> ()

let lemma_array_lemma (#base:sort -> Type0) (s:S.checked_schema)
                      (bc:S.boolean_carrier base) (core:T.scalar_model base)
                      (other:V.interpretation base (S.signature s))
                      (m:family base (S.signature s))
                      (scope:list sort) (rho:V.environment base (S.signature s) scope)
                      (e:expr)
  : Lemma (requires model s bc core other m /\ D.scoped scope e /\
                    supported m e /\ A.array_lemma e)
          (ensures T.truth_at s bc core other scope rho e) =
  match A.equality_parts e with
  | Some (a, b) ->
    T.lemma_equality_at s bc core other scope rho a b;
    if A.read_over_write_same a b then
      lemma_read_over_write_same s bc core other m scope rho a b
    else lemma_read_over_write_same s bc core other m scope rho b a
  | None ->
    (match e with
     | App f [p; q] ->
       if A.array_clause p q then lemma_array_clause s bc core other m scope rho p q
       else lemma_array_clause s bc core other m scope rho q p;
       assert (e == App (Z3ClauseSyntax.or_decl [p; q]) [p; q]);
       BR.lemma_or_at s bc core other scope rho p q
     | _ -> ())

let lemma_store_redundant (#base:sort -> Type0) (s:S.checked_schema)
                          (bc:S.boolean_carrier base) (core:T.scalar_model base)
                          (other:V.interpretation base (S.signature s))
                          (m:family base (S.signature s))
                          (scope:list sort) (rho:V.environment base (S.signature s) scope)
                          (f:func_decl) (a k v:expr)
  : Lemma (requires model s bc core other m /\ D.scoped scope (App f [a; k; v]) /\
                    supported m (App f [a; k; v]) /\
                    A.store_app f a k v /\ A.select_parts v == Some (a, k))
          (ensures T.evaluate_at s bc core other scope rho (App f [a; k; v]) ==
                   T.evaluate_at s bc core other scope rho a) =
  match get_sort a, v with
  | ArraySort [index] element, App _ [_; _] ->
    lemma_select s bc core other m scope rho index element a k;
    lemma_store s bc core other m scope rho index element a k v;
    lemma_redundant (m.arrays index element)
      (T.evaluate_at s bc core other scope rho a)
      (T.evaluate_at s bc core other scope rho k)
  | _, _ -> ()

let lemma_store_parts_scope (scope:list sort) (e a k v:expr)
  : Lemma (requires D.scoped scope e /\ A.store_parts e == Some (a, k, v))
          (ensures D.scoped scope a /\ D.scoped scope k /\ D.scoped scope v /\
                   (match get_sort a with
                    | ArraySort [index] element ->
                      e == App (store_decl index element) [a; k; v] /\
                      get_sort k == index /\ get_sort v == element
                    | _ -> False)) =
  match e with
  | App _ [_; _; _] ->
    assert (D.scoped_args scope [a; k; v]);
    assert (D.scoped_args scope [k; v]);
    assert (D.scoped_args scope [v]);
    (match get_sort a with ArraySort [_] _ -> () | _ -> ())
  | _ -> ()

let lemma_store_contract (#base:sort -> Type0) (s:S.checked_schema)
                         (bc:S.boolean_carrier base) (core:T.scalar_model base)
                         (other:V.interpretation base (S.signature s))
                         (m:family base (S.signature s))
                         (scope:list sort) (rho:V.environment base (S.signature s) scope)
                         (e t:expr)
  : Lemma (requires model s bc core other m /\ D.scoped scope e /\ D.scoped scope t /\
                    supported m e /\ A.store_contract e == Some t)
          (ensures T.evaluate_at s bc core other scope rho e ==
                   T.evaluate_at s bc core other scope rho t) =
  match e with
  | App f [a; k; v] ->
    (match A.store_parts a with
     | Some (original, j, w) ->
       lemma_store_parts_scope scope a original j w;
       if k = j then (
         match get_sort a with
         | ArraySort [index] element ->
           lemma_store s bc core other m scope rho index element original j w;
           lemma_store s bc core other m scope rho index element a k v;
           lemma_store s bc core other m scope rho index element original k v;
           lemma_overwrite (m.arrays index element)
             (T.evaluate_at s bc core other scope rho original)
             (T.evaluate_at s bc core other scope rho k)
             (T.evaluate_at s bc core other scope rho w)
             (T.evaluate_at s bc core other scope rho v)
         | _ -> ())
       else lemma_store_redundant s bc core other m scope rho f a k v
     | None -> lemma_store_redundant s bc core other m scope rho f a k v)
  | _ -> ()

let lemma_ite_scope (scope:list sort) (e c t u:expr)
  : Lemma (requires D.scoped scope e /\ A.ite_parts e == Some (c, t, u))
          (ensures D.scoped scope c /\ D.scoped scope t /\ D.scoped scope u /\
                   get_sort c == bool_sort /\ get_sort t == get_sort u)
  = match e with
    | App _ [_; _; _] ->
      assert (D.scoped_args scope [c; t; u]);
      assert (D.scoped_args scope [t; u]);
      assert (D.scoped_args scope [u])
    | _ -> ()

let lemma_ite_supported (#base:sort -> Type0) (#sigma:V.signature)
                          (m:family base sigma) (e c t u:expr)
  : Lemma (requires supported m e /\ A.ite_parts e == Some (c, t, u))
            (ensures supported m c /\ supported m t /\ supported m u) =
  match e with
  | App _ [_; _; _] ->
      assert (supported_args m [c; t; u]);
      assert (supported_args m [t; u]);
      assert (supported_args m [u])
  | _ -> ()

let lemma_ite (#base:sort -> Type0) (s:S.checked_schema)
              (bc:S.boolean_carrier base) (core:T.scalar_model base)
              (other:V.interpretation base (S.signature s))
              (scope:list sort) (rho:V.environment base (S.signature s) scope)
              (e c t u:expr)
  : Lemma (requires D.scoped scope e /\ D.scoped scope t /\ D.scoped scope u /\
                    A.ite_parts e == Some (c, t, u))
          (ensures T.evaluate_at s bc core other scope rho e ==
                   (if T.truth_at s bc core other scope rho c
                    then T.evaluate_at s bc core other scope rho t
                    else T.evaluate_at s bc core other scope rho u)) =
  lemma_ite_scope scope e c t u;
  match e with
  | App f [_; _; _] ->
    assert (f == A.term_ite_decl (get_sort t));
    assert (T.classify f == T.Choice (get_sort t));
    T.lemma_evaluate_core_at s bc core other scope rho f [c; t; u];
    let cv = T.evaluate_at s bc core other scope rho c in
    let tv = T.evaluate_at s bc core other scope rho t in
    let uv = T.evaluate_at s bc core other scope rho u in
    assert (T.evaluate_arguments_at s bc core other scope rho [u] [get_sort t] == [uv]);
    assert (T.evaluate_arguments_at s bc core other scope rho [t; u]
              [get_sort t; get_sort t] == [tv; uv]);
    assert (T.evaluate_arguments_at s bc core other scope rho [c; t; u] f.domain == [cv; tv; uv])
  | _ -> ()

let lemma_ite_contract (#base:sort -> Type0) (s:S.checked_schema)
                       (bc:S.boolean_carrier base) (core:T.scalar_model base)
                       (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (e result:expr)
  : Lemma (requires D.scoped scope e /\ D.scoped scope result /\ A.ite_contract e == Some result)
          (ensures T.evaluate_at s bc core other scope rho e ==
                   T.evaluate_at s bc core other scope rho result) =
  match A.ite_parts e with
  | Some (c, t, u) ->
    lemma_ite_scope scope e c t u;
    lemma_ite s bc core other scope rho e c t u;
    BR.lemma_cut s bc core other scope rho [] 0 c
  | None -> ()

let lemma_ite_equivalent (#base:sort -> Type0) (s:S.checked_schema)
                         (bc:S.boolean_carrier base) (core:T.scalar_model base)
                         (other:V.interpretation base (S.signature s))
                         (scope:list sort) (rho:V.environment base (S.signature s) scope)
                         (e result:expr)
  : Lemma (requires D.scoped scope e /\ D.scoped scope result /\ A.ite_equivalent e result)
          (ensures T.evaluate_at s bc core other scope rho e ==
                   T.evaluate_at s bc core other scope rho result) =
  match A.ite_parts e, A.ite_parts result with
  | Some (c, a, b), Some (d, u, v) ->
    lemma_ite_scope scope e c a b;
    lemma_ite_scope scope result d u v;
    lemma_ite s bc core other scope rho e c a b;
    lemma_ite s bc core other scope rho result d u v;
    if a = u && b = v && Z3BooleanRewriteSyntax.boolean_equiv 8 10 c d then
      BR.lemma_equivalent s bc core other scope rho 8 10 c d
    else (
      BR.lemma_not_at s bc core other scope rho c;
      BR.lemma_not_at s bc core other scope rho d;
      if c <> Z3ClauseSyntax.mk_not_expr d && d <> Z3ClauseSyntax.mk_not_expr c then (
        BR.lemma_equivalent s bc core other scope rho 8 10 c (Z3ClauseSyntax.mk_not_expr d)))
  | _, _ -> ()

let lemma_ite_merge (#base:sort -> Type0) (s:S.checked_schema)
                    (bc:S.boolean_carrier base) (core:T.scalar_model base)
                    (other:V.interpretation base (S.signature s))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope)
                    (e result:expr)
  : Lemma (requires D.scoped scope e /\ D.scoped scope result /\ A.ite_merge e == Some result)
          (ensures T.evaluate_at s bc core other scope rho e ==
                   T.evaluate_at s bc core other scope rho result) =
  match A.ite_parts e with
  | Some (c, t, u) ->
    lemma_ite_scope scope e c t u;
    lemma_ite s bc core other scope rho e c t u;
    (match A.ite_parts u with
     | Some (d, a, b) ->
       lemma_ite_scope scope u d a b;
       lemma_ite s bc core other scope rho u d a b;
       let condition = App (Z3ClauseSyntax.or_decl [c; d]) [c; d] in
       lemma_ite s bc core other scope rho result condition t b;
       BR.lemma_or_at s bc core other scope rho c d
     | None ->
       (match A.ite_parts t with
        | Some (d, a, b) ->
          lemma_ite_scope scope t d a b;
          lemma_ite s bc core other scope rho t d a b;
          let condition = App (Z3ClauseSyntax.and_decl [c; d]) [c; d] in
          lemma_ite s bc core other scope rho result condition a u;
          BR.lemma_connective_at s bc core other scope rho Z3BooleanRewriteSyntax.Conjunction [c; d]
        | None -> ()))
  | None -> ()

let lemma_read_contract (#base:sort -> Type0) (s:S.checked_schema)
                        (bc:S.boolean_carrier base) (core:T.scalar_model base)
                        (other:V.interpretation base (S.signature s))
                        (m:family base (S.signature s))
                        (scope:list sort) (rho:V.environment base (S.signature s) scope)
                        (e result:expr)
  : Lemma (requires model s bc core other m /\ D.scoped scope e /\ D.scoped scope result /\
                    supported m e /\ supported m result /\ A.read_contract e == Some result)
          (ensures T.evaluate_at s bc core other scope rho e ==
                   T.evaluate_at s bc core other scope rho result) =
  assert (A.read_over_write_same e result);
  lemma_read_over_write_same s bc core other m scope rho e result

let lemma_contract (#base:sort -> Type0) (s:S.checked_schema)
                   (bc:S.boolean_carrier base) (core:T.scalar_model base)
                   (other:V.interpretation base (S.signature s))
                   (m:family base (S.signature s))
                   (scope:list sort) (rho:V.environment base (S.signature s) scope)
                   (e result:expr)
  : Lemma (requires model s bc core other m /\ D.scoped scope e /\ D.scoped scope result /\
                    supported m e /\ supported m result /\ A.contract e == Some result)
          (ensures T.evaluate_at s bc core other scope rho e ==
                   T.evaluate_at s bc core other scope rho result) =
  match A.store_contract e with
  | Some _ -> lemma_store_contract s bc core other m scope rho e result
  | None ->
    (match A.read_contract e with
     | Some _ -> lemma_read_contract s bc core other m scope rho e result
     | None -> lemma_ite_contract s bc core other scope rho e result)

let lemma_expand_read (#base:sort -> Type0) (s:S.checked_schema)
                      (bc:S.boolean_carrier base) (core:T.scalar_model base)
                      (other:V.interpretation base (S.signature s))
                      (m:family base (S.signature s))
                      (scope:list sort) (rho:V.environment base (S.signature s) scope)
                      (e result:expr)
  : Lemma (requires model s bc core other m /\ D.scoped scope e /\ D.scoped scope result /\
                    supported m e /\ A.expand_read e == Some result)
          (ensures T.evaluate_at s bc core other scope rho e ==
                   T.evaluate_at s bc core other scope rho result) =
  match e with
  | App _ [stored; k] ->
    (match A.store_parts stored with
     | Some (base, j, v) ->
       lemma_store_parts_scope scope stored base j v;
       (match get_sort base with
        | ArraySort [index] element ->
          assert (stored == App (store_decl index element) [base; j; v]);
          assert (e == App (select_decl index element) [stored; k]);
          lemma_store s bc core other m scope rho index element base j v;
          lemma_select s bc core other m scope rho index element stored k;
          lemma_select s bc core other m scope rho index element base k;
          T.lemma_equality_at s bc core other scope rho j k;
          lemma_ite s bc core other scope rho result (Z3ClauseSyntax.mk_eq_expr j k)
            v (App (select_decl index element) [base; k]);
          let jv = T.evaluate_at s bc core other scope rho j in
          let kv = T.evaluate_at s bc core other scope rho k in
          let av = T.evaluate_at s bc core other scope rho base in
          let vv = T.evaluate_at s bc core other scope rho v in
          assert (T.evaluate_at s bc core other scope rho e ==
                  (m.arrays index element).read ((m.arrays index element).write av jv vv) kv);
          if ID.strong_excluded_middle (jv == kv) then ()
          else (
            lemma_read_other (m.arrays index element) av jv kv vv;
            assert (T.evaluate_at s bc core other scope rho result ==
                    (m.arrays index element).read av kv))
        | _ -> ())
     | None -> ())
  | _ -> ()

let lemma_contract_shape (#base:sort -> Type0) (#sigma:V.signature)
                         (m:family base sigma) (scope:list sort) (e result:expr)
  : Lemma (requires D.scoped scope e /\ supported m e /\ A.contract e == Some result)
          (ensures D.scoped scope result /\ supported m result /\
                   get_sort result == get_sort e) =
  match A.store_contract e with
  | Some _ ->
    (match e with
     | App _ [a; k; v] ->
       lemma_store_parts_scope scope e a k v;
       (match A.store_parts a with
        | Some (original, j, w) ->
          lemma_store_parts_scope scope a original j w;
          if k = j then (
            match get_sort original with
            | ArraySort [index] element ->
              lemma_scope_store scope index element original k v
            | _ -> ())
        | None -> ())
     | _ -> ())
  | None ->
    (match A.read_contract e with
     | Some _ ->
       (match A.select_parts e with
        | Some (a, _) ->
          (match A.store_parts a with
           | Some (original, j, v) ->
             lemma_store_parts_scope scope a original j v
           | None -> ())
        | None -> ())
     | None ->
       (match A.ite_parts e with
        | Some (c, t, u) -> lemma_ite_scope scope e c t u
        | None -> ()))

let lemma_ite_merge_shape (#base:sort -> Type0) (#sigma:V.signature)
                          (m:family base sigma) (scope:list sort) (e result:expr)
  : Lemma (requires D.scoped scope e /\ supported m e /\ A.ite_merge e == Some result)
          (ensures D.scoped scope result /\ supported m result /\
                   get_sort result == get_sort e) =
  match A.ite_parts e with
  | Some (c, t, u) ->
    lemma_ite_scope scope e c t u;
    lemma_ite_supported m e c t u;
    (match A.ite_parts u with
     | Some (d, a, b) ->
       lemma_ite_scope scope u d a b;
       lemma_ite_supported m u d a b;
       lemma_boolean_pair_shape m scope Z3BooleanRewriteSyntax.Disjunction c d;
       lemma_ite_shape m scope (App (Z3ClauseSyntax.or_decl [c; d]) [c; d]) t b
     | None ->
       (match A.ite_parts t with
        | Some (d, a, b) ->
          lemma_ite_scope scope t d a b;
          lemma_ite_supported m t d a b;
          lemma_boolean_pair_shape m scope Z3BooleanRewriteSyntax.Conjunction c d;
          lemma_ite_shape m scope (App (Z3ClauseSyntax.and_decl [c; d]) [c; d]) a u
        | None -> ()))
  | None -> ()

let lemma_expand_read_shape (#base:sort -> Type0) (#sigma:V.signature)
                            (m:family base sigma) (scope:list sort) (e result:expr)
  : Lemma (requires D.scoped scope e /\ supported m e /\ A.expand_read e == Some result)
          (ensures D.scoped scope result /\ supported m result /\
                   get_sort result == get_sort e) =
  match e with
  | App _ [stored; k] ->
    (match A.store_parts stored with
     | Some (base, j, v) ->
       lemma_store_parts_scope scope stored base j v;
       (match get_sort base with
        | ArraySort [index] element ->
          lemma_scope_select scope index element base k;
          V.lemma_sort_eq (get_sort j) (get_sort j);
          V.lemma_sort_eq (get_sort k) (get_sort j);
          assert (D.scoped scope (Z3ClauseSyntax.mk_eq_expr j k));
          assert (supported m (Z3ClauseSyntax.mk_eq_expr j k));
          lemma_ite_shape m scope (Z3ClauseSyntax.mk_eq_expr j k) v
            (App (select_decl index element) [base; k])
        | _ -> ())
     | None -> ())
  | _ -> ()

let lemma_equality_parts_scope (scope:list sort) (e a b:expr)
  : Lemma (requires D.scoped scope e /\ A.equality_parts e == Some (a, b))
          (ensures D.scoped scope a /\ D.scoped scope b /\
                   get_sort a == get_sort b /\ get_sort e == bool_sort /\
                   e == Z3ClauseSyntax.mk_eq_expr a b) =
  match e with
  | App _ [_; _] ->
    assert (D.scoped_args scope [a; b]);
    assert (D.scoped_args scope [b])
  | _ -> ()

let rec lemma_equivalent (#base:sort -> Type0) (schema:S.checked_schema)
                         (bc:S.boolean_carrier base) (core:T.scalar_model base)
                         (other:V.interpretation base (S.signature schema))
                         (m:family base (S.signature schema))
                         (scope:list sort) (rho:V.environment base (S.signature schema) scope)
                         (fuel:nat) (a b:expr)
  : Lemma (requires model schema bc core other m /\
                    D.scoped scope a /\ D.scoped scope b /\
                    supported m a /\ supported m b /\ A.equivalent fuel a b)
          (ensures T.evaluate_at schema bc core other scope rho a ==
                   T.evaluate_at schema bc core other scope rho b)
          (decreases %[fuel; 0]) =
  if a = b || fuel = 0 then ()
  else
    let _ = assert (fuel > 0) in
    if A.ite_equivalent a b then lemma_ite_equivalent schema bc core other scope rho a b
    else match A.contract a, A.contract b with
    | Some c, _ ->
      lemma_contract_shape m scope a c;
      lemma_contract schema bc core other m scope rho a c;
      lemma_equivalent schema bc core other m scope rho (fuel - 1) c b
    | None, Some d ->
      lemma_contract_shape m scope b d;
      lemma_contract schema bc core other m scope rho b d;
      lemma_equivalent schema bc core other m scope rho (fuel - 1) a d
    | None, None ->
      let congruent =
        match a, b with
        | App f xs, App g ys -> f = g && A.equivalent_args (fuel - 1) xs ys
        | _, _ -> false in
      if congruent then (
        match a, b with
        | App f xs, App _ ys ->
          lemma_equivalent_args schema bc core other m scope rho (fuel - 1) xs ys f.domain
        | _, _ -> ())
      else
        let symmetric =
          match A.equality_parts a, A.equality_parts b with
          | Some (x, y), Some (u, v) ->
            A.equivalent (fuel - 1) x v && A.equivalent (fuel - 1) y u
          | _, _ -> false in
        if symmetric then (
          match A.equality_parts a, A.equality_parts b with
          | Some (x, y), Some (u, v) ->
            lemma_equality_parts_scope scope a x y;
            lemma_equality_parts_scope scope b u v;
            lemma_equivalent schema bc core other m scope rho (fuel - 1) x v;
            lemma_equivalent schema bc core other m scope rho (fuel - 1) y u;
            T.lemma_equality_at schema bc core other scope rho x y;
            T.lemma_equality_at schema bc core other scope rho u v;
            T.lemma_boolean schema bc (T.evaluate_at schema bc core other scope rho a);
            T.lemma_boolean schema bc (T.evaluate_at schema bc core other scope rho b)
          | _, _ -> ())
        else match A.expand_read a, A.expand_read b with
        | Some c, _ ->
          lemma_expand_read_shape m scope a c;
          lemma_expand_read schema bc core other m scope rho a c;
          lemma_equivalent schema bc core other m scope rho (fuel - 1) c b
        | None, Some d ->
          lemma_expand_read_shape m scope b d;
          lemma_expand_read schema bc core other m scope rho b d;
          lemma_equivalent schema bc core other m scope rho (fuel - 1) a d
        | None, None ->
          let merged =
            match A.ite_merge a, A.ite_merge b with
            | Some c, _ -> A.equivalent (fuel - 1) c b
            | None, Some d -> A.equivalent (fuel - 1) a d
            | None, None -> false in
          if merged then (
            match A.ite_merge a, A.ite_merge b with
            | Some c, _ ->
              lemma_ite_merge_shape m scope a c;
              lemma_ite_merge schema bc core other scope rho a c;
              lemma_equivalent schema bc core other m scope rho (fuel - 1) c b
            | None, Some d ->
              lemma_ite_merge_shape m scope b d;
              lemma_ite_merge schema bc core other scope rho b d;
              lemma_equivalent schema bc core other m scope rho (fuel - 1) a d
            | None, None -> ())
          else
            (match A.ite_parts a, A.ite_parts b with
             | Some (c, x, y), _ ->
               lemma_ite_scope scope a c x y;
               lemma_ite_supported m a c x y;
               lemma_ite schema bc core other scope rho a c x y;
               lemma_equivalent schema bc core other m scope rho (fuel - 1) x b;
               lemma_equivalent schema bc core other m scope rho (fuel - 1) y b
             | None, Some (c, x, y) ->
               lemma_ite_scope scope b c x y;
               lemma_ite_supported m b c x y;
               lemma_ite schema bc core other scope rho b c x y;
               lemma_equivalent schema bc core other m scope rho (fuel - 1) a x;
               lemma_equivalent schema bc core other m scope rho (fuel - 1) a y
             | None, None -> ())

and lemma_equivalent_args (#base:sort -> Type0) (schema:S.checked_schema)
                          (bc:S.boolean_carrier base) (core:T.scalar_model base)
                          (other:V.interpretation base (S.signature schema))
                          (m:family base (S.signature schema))
                          (scope:list sort) (rho:V.environment base (S.signature schema) scope)
                          (fuel:nat) (xs ys:list expr) (ss:list sort)
  : Lemma (requires model schema bc core other m /\
                    D.scoped_args scope xs /\ D.scoped_args scope ys /\
                    supported_args m xs /\ supported_args m ys /\
                    sorts_match xs ss /\ sorts_match ys ss /\ A.equivalent_args fuel xs ys)
          (ensures T.evaluate_arguments_at schema bc core other scope rho xs ss ==
                   T.evaluate_arguments_at schema bc core other scope rho ys ss)
          (decreases %[fuel; FStar.List.Tot.length xs + 1]) =
  match xs, ys, ss with
  | x :: rest, y :: rest', _ :: sorts ->
    lemma_equivalent schema bc core other m scope rho fuel x y;
    lemma_equivalent_args schema bc core other m scope rho fuel rest rest' sorts
  | _, _, _ -> ()
