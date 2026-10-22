module Z3SortedDatatype

open Z3AstTheory
open Z3ValueTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module R = Z3ResolutionProofTheory
module B = Z3BoundedBoolEquiv
module BR = Z3BooleanRewrite
module D = Z3Definitions
module L = FStar.List.Tot
module N = Z3BooleanNormalForm

let rec lemma_recognizer_tag (f:func_decl) (cs:list S.constructor_case)
  : Lemma (requires Some? (S.find_recognizer f cs))
          (ensures f.interp == Some Z3DatatypeLemma.op_recognizer)
          (decreases cs) =
  match cs with
  | [] -> ()
  | c :: rest ->
    (match S.constructor_id c.constructor with
     | Some (owner, tag) ->
       if Z3DatatypeLemma.recognizer f (Var 0 c.constructor.range) <> Some (owner, tag)
       then lemma_recognizer_tag f rest
     | None -> lemma_recognizer_tag f rest)

let rec lemma_accessor_tag (f:func_decl) (cs:list S.constructor_case)
  : Lemma (requires Some? (S.find_accessor f cs))
          (ensures f.interp == Some Z3DatatypeLemma.op_accessor)
          (decreases cs) =
  match cs with
  | [] -> ()
  | c :: rest ->
    (match S.constructor_id c.constructor, Z3DatatypeLemma.accessor f (Var 0 c.constructor.range) with
     | Some _, Some _ -> ()
     | _, _ -> lemma_accessor_tag f rest)

let lemma_recognizer_dispatch (s:S.checked_schema) (f:func_decl)
  : Lemma (requires Some? (S.find_recognizer f s.cases))
          (ensures T.classify f == T.Other /\ not (L.mem f (S.signature s))) =
  lemma_recognizer_tag f s.cases;
  if L.mem f (S.signature s) then T.lemma_registered_constructor s f

let lemma_accessor_dispatch (s:S.checked_schema) (f:func_decl)
  : Lemma (requires Some? (S.find_accessor f s.cases))
          (ensures T.classify f == T.Other /\ not (L.mem f (S.signature s)) /\
                   S.find_recognizer f s.cases == None) =
  lemma_accessor_tag f s.cases;
  if L.mem f (S.signature s) then T.lemma_registered_constructor s f;
  match S.find_recognizer f s.cases with
  | Some _ -> lemma_recognizer_tag f s.cases
  | None -> ()

let lemma_recognizer (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                     (f:func_decl) (arg:expr)
  : Lemma (requires Some? (S.find_recognizer f s.cases) /\ D.scoped [] (App f [arg]))
          (ensures T.truth s bc eq other (App f [arg]) ==
                   V.recognize (Some?.v (S.find_recognizer f s.cases)).constructor
                     (T.evaluate s bc eq other arg)) =
  lemma_recognizer_dispatch s f

let rec lemma_arguments_index (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                          (args:list expr) (ss:list sort) (n:nat)
  : Lemma (requires D.scoped_args [] args /\ sorts_match args ss /\ n < L.length ss)
          (ensures n < L.length args /\
                   n < L.length (T.evaluate_arguments s bc eq other args ss) /\
                   D.scoped [] (L.index args n) /\
                   get_sort (L.index args n) == L.index ss n /\
                   L.index (T.evaluate_arguments s bc eq other args ss) n ==
                     T.evaluate s bc eq other (L.index args n))
          (decreases args) =
  match args, ss with
  | a :: rest, t :: tail ->
    V.lemma_sort_eq (get_sort a) t;
    if n > 0 then lemma_arguments_index s bc eq other rest tail (n - 1)
  | _, _ -> ()

let lemma_accessor (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                   (f:func_decl) (g:func_decl) (args:list expr)
  : Lemma (requires Some? (S.find_accessor f s.cases) /\
                    g == (Some?.v (S.find_accessor f s.cases)).matched_case.constructor /\
                    L.mem g (S.signature s) /\ D.scoped [] (App f [App g args]))
          (ensures
            (let r = Some?.v (S.find_accessor f s.cases) in
             r.field < L.length args /\
             D.scoped [] (L.index args r.field) /\
             T.evaluate s bc eq other (App f [App g args]) ==
             T.evaluate s bc eq other (L.index args r.field))) =
  let r = Some?.v (S.find_accessor f s.cases) in
  lemma_accessor_dispatch s f;
  V.lemma_fields_index (S.signature s) g.domain
    (T.evaluate_arguments s bc eq other args g.domain) r.field;
  lemma_arguments_index s bc eq other args g.domain r.field

let rec field_equalities (xs ys:list expr) : Tot (list expr) (decreases xs) =
  match xs, ys with
  | x :: rest, y :: tail -> R.mk_eq_expr x y :: field_equalities rest tail
  | _, _ -> []

let rec lemma_field_equalities (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                               (xs ys:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args [] xs /\ D.scoped_args [] ys /\
                    sorts_match xs ss /\ sorts_match ys ss)
          (ensures D.scoped_args [] (field_equalities xs ys) /\
                   (forall (e:expr). L.mem e (field_equalities xs ys) ==> get_sort e == bool_sort) /\
                   (T.evaluate_arguments s bc eq other xs ss ==
                    T.evaluate_arguments s bc eq other ys ss <==>
                    B.eval_args (T.truth s bc eq other) B.And (L.map B.Atom (field_equalities xs ys))))
          (decreases xs) =
  match xs, ys, ss with
  | x :: rest, y :: tail, t :: remaining ->
    V.lemma_sort_eq (get_sort x) t;
    V.lemma_sort_eq (get_sort y) t;
    T.lemma_equality s bc eq other x y;
    lemma_field_equalities s bc eq other rest tail remaining
  | _, _, _ -> ()

let rewrite (s:S.checked_schema) (e:expr) : option expr =
  match e with
  | App f [condition; a; b] ->
    if T.classify f = T.Choice (get_sort a) then
      if condition = R.true_expr then Some a
      else if condition = R.false_expr || a = b then Some b
      else None
    else None
  | App f [App g args] ->
    if not (L.mem g (S.signature s)) then None
    else (match S.find_recognizer f s.cases with
      | Some c -> Some (if c.constructor = g then R.true_expr else R.false_expr)
      | None ->
        (match S.find_accessor f s.cases with
         | Some r ->
           if r.matched_case.constructor = g && r.field < L.length args
           then Some (L.index args r.field) else None
         | None -> None))
  | App f [App g xs; App h ys] ->
    if f = R.eq_decl g.range && g.range = h.range &&
       L.mem g (S.signature s) && L.mem h (S.signature s) then
      if g <> h then Some R.false_expr
      else let fields = field_equalities xs ys in
        Some (App (BR.connective_decl BR.Conjunction fields) fields)
    else None
  | _ -> None

let rec lemma_boolean_domain (es:list expr)
  : Lemma (requires forall (e:expr). L.mem e es ==> get_sort e == bool_sort)
          (ensures T.boolean_sorts (BR.boolean_domain es) /\ sorts_match es (BR.boolean_domain es))
          (decreases es) =
  match es with [] -> () | _ :: rest -> lemma_boolean_domain rest

let lemma_conjunction (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                      (es:list expr)
  : Lemma (requires D.scoped_args [] es /\
                    (forall (e:expr). L.mem e es ==> get_sort e == bool_sort))
          (ensures T.truth s bc eq other (App (BR.connective_decl BR.Conjunction es) es) ==
                   B.eval_args (T.truth s bc eq other) B.And (L.map B.Atom es)) =
  lemma_boolean_domain es;
  T.lemma_evaluate_core s bc eq other (BR.connective_decl BR.Conjunction es) es;
  T.lemma_boolean_arguments s bc eq other es (BR.boolean_domain es) B.And

let lemma_rewrite (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                  (e result:expr)
  : Lemma (requires D.scoped [] e /\ D.scoped [] result /\
                    get_sort e == get_sort result /\ rewrite s e == Some result)
          (ensures T.evaluate s bc eq other e == T.evaluate s bc eq other result) =
  match e with
  | App f [condition; a; b] ->
    T.lemma_evaluate_core s bc eq other f [condition; a; b];
    if condition = R.true_expr || condition = R.false_expr then
      T.lemma_cut s bc eq other 1 condition
  | App f [App g args] ->
    (match S.find_recognizer f s.cases with
     | Some c ->
       lemma_recognizer s bc eq other f (App g args);
       T.lemma_boolean s bc (T.evaluate s bc eq other e);
       T.lemma_evaluate_core s bc eq other
         (match result with App h _ -> h | _ -> f) []
     | None ->
       (match S.find_accessor f s.cases with
        | Some _ -> lemma_accessor s bc eq other f g args
        | None -> ()))
  | App f [App g xs; App h ys] ->
    T.lemma_equality s bc eq other (App g xs) (App h ys);
    if g = h then (
      lemma_field_equalities s bc eq other xs ys g.domain;
      lemma_conjunction s bc eq other (field_equalities xs ys))
    else T.lemma_evaluate_core s bc eq other
      (match R.false_expr with App k _ -> k | _ -> f) [];
    T.lemma_boolean s bc (T.evaluate s bc eq other e);
    T.lemma_boolean s bc (T.evaluate s bc eq other result)
  | _ -> ()

let rec normalize (s:S.checked_schema) (fuel:nat) (e:expr)
  : Tot (option expr) (decreases %[fuel; e]) =
  if fuel = 0 || not (D.scoped [] e) then None
  else
    let next = fuel - 1 in
    let rebuilt =
      match e with
      | App f args ->
        (match normalize_args s next args with
         | Some es -> Some (App f es)
         | None -> None)
      | _ -> Some e in
    match rebuilt with
    | None -> None
    | Some source ->
      if not (D.scoped [] source && get_sort source = get_sort e) then None
      else
        let target = match rewrite s source with Some result -> result | None -> source in
        if not (D.scoped [] target && get_sort target = get_sort source) then None
        else if target = source then Some target
        else normalize s next target

and normalize_args (s:S.checked_schema) (fuel:nat) (es:list expr)
  : Tot (option (list expr)) (decreases %[fuel; es]) =
  match es with
  | [] -> Some []
  | e :: rest ->
    (match normalize s fuel e, normalize_args s fuel rest with
     | Some x, Some xs -> Some (x :: xs)
     | _, _ -> None)

let rec lemma_normalize (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                        (fuel:nat) (e result:expr)
  : Lemma (requires D.scoped [] e /\ normalize s fuel e == Some result)
          (ensures D.scoped [] result /\ get_sort result == get_sort e /\
                   T.evaluate s bc eq other e == T.evaluate s bc eq other result)
          (decreases %[fuel; e]) =
  if fuel = 0 then ()
  else
    let next = fuel - 1 in
    let source =
      match e with
      | App f args ->
        let es = Some?.v (normalize_args s next args) in
        lemma_normalize_args s bc eq other next args es f.domain;
        App f es
      | _ -> e in
    assert (T.evaluate s bc eq other e == T.evaluate s bc eq other source);
    let target = match rewrite s source with Some x -> x | None -> source in
    (match rewrite s source with Some _ -> lemma_rewrite s bc eq other source target | None -> ());
    if target <> source then lemma_normalize s bc eq other next target result

and lemma_normalize_args (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                         (fuel:nat) (xs ys:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args [] xs /\ sorts_match xs ss /\
                    normalize_args s fuel xs == Some ys)
          (ensures D.scoped_args [] ys /\ sorts_match ys ss /\
                   T.evaluate_arguments s bc eq other xs ss == T.evaluate_arguments s bc eq other ys ss)
          (decreases %[fuel; xs]) =
  match xs, ys, ss with
  | x :: rest, y :: tail, t :: remaining ->
    V.lemma_sort_eq (get_sort x) t;
    lemma_normalize s bc eq other fuel x y;
    V.lemma_sort_eq (get_sort y) t;
    lemma_normalize_args s bc eq other fuel rest tail remaining
  | _, _, _ -> ()

let recognizer_of (s:S.checked_schema) (subject:expr) (constructor:func_decl) (e:expr) : bool =
  match e with
  | App f [arg] ->
    arg = subject &&
    (match S.find_recognizer f s.cases with Some c -> c.constructor = constructor | None -> false)
  | _ -> false

let rec has_recognizer (s:S.checked_schema) (subject:expr) (constructor:func_decl) (es:list expr)
  : Tot bool (decreases es) =
  match es with
  | [] -> false
  | e :: rest -> recognizer_of s subject constructor e || has_recognizer s subject constructor rest

let rec covered (s:S.checked_schema) (subject:expr) (constructors:list func_decl) (es:list expr)
  : Tot bool (decreases constructors) =
  match constructors with
  | [] -> true
  | c :: rest -> has_recognizer s subject c es && covered s subject rest es

let rec subject_of (s:S.checked_schema) (es:list expr) : Tot (option expr) (decreases es) =
  match es with
  | [] -> None
  | App f [arg] :: rest ->
    if Some? (S.find_recognizer f s.cases) then Some arg else subject_of s rest
  | _ :: rest -> subject_of s rest

let exhaustive (s:S.checked_schema) (e:expr) : bool =
  match e with
  | App f es ->
    T.classify f = T.Nary B.Or &&
    (match subject_of s es with
     | Some subject ->
       V.datatype_sort (S.signature s) (get_sort subject) &&
       covered s subject (V.constructors_of (S.signature s) (get_sort subject)) es
     | None -> false)
  | _ -> false

let rec lemma_subject (s:S.checked_schema) (es:list expr)
  : Lemma (requires D.scoped_args [] es /\ Some? (subject_of s es))
          (ensures D.scoped [] (Some?.v (subject_of s es)))
          (decreases es) =
  match es with
  | [] -> ()
  | App f [_] :: rest ->
    if not (Some? (S.find_recognizer f s.cases)) then lemma_subject s rest
  | _ :: rest -> lemma_subject s rest

let rec lemma_covered (s:S.checked_schema) (subject:expr)
                      (constructors:list func_decl) (es:list expr) (f:func_decl)
  : Lemma (requires covered s subject constructors es /\ L.mem f constructors)
          (ensures has_recognizer s subject f es)
          (decreases constructors) =
  match constructors with
  | [] -> ()
  | c :: rest -> if c <> f then lemma_covered s subject rest es f

let rec lemma_has_recognizer (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                             (subject:expr) (f:func_decl) (es:list expr)
  : Lemma (requires D.scoped [] subject /\ D.scoped_args [] es /\
                    V.recognize f (T.evaluate s bc eq other subject) /\
                    has_recognizer s subject f es)
          (ensures B.eval_args (T.truth s bc eq other) B.Or (L.map B.Atom es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    if recognizer_of s subject f e then
      (match e with App g [_] -> lemma_recognizer s bc eq other g subject | _ -> ())
    else lemma_has_recognizer s bc eq other subject f rest

let lemma_exhaustive (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                     (e:expr)
  : Lemma (requires D.scoped [] e /\ exhaustive s e)
          (ensures T.truth s bc eq other e) =
  match e with
  | App f es ->
    lemma_subject s es;
    let subject = Some?.v (subject_of s es) in
    let v = T.evaluate s bc eq other subject in
    (match v with
     | V.Constructor g _ ->
       V.lemma_constructor_member (S.signature s) (get_sort subject) g;
       lemma_covered s subject (V.constructors_of (S.signature s) (get_sort subject)) es g;
       lemma_has_recognizer s bc eq other subject g es
     | V.Scalar _ _ -> ());
    T.lemma_nary s bc eq other f es B.Or
  | _ -> ()

let selector_of (s:S.checked_schema) (constructor:func_decl)
                (subject:expr) (index:nat) (e:expr) : bool =
  match e with
  | App f [arg] ->
    arg = subject &&
    (match S.find_accessor f s.cases with
     | Some r -> r.matched_case.constructor = constructor && r.field = index
     | None -> false)
  | _ -> false

let rec selectors (s:S.checked_schema) (constructor:func_decl)
                  (subject:expr) (index:nat) (es:list expr)
  : Tot bool (decreases es) =
  match es with
  | [] -> true
  | e :: rest -> selector_of s constructor subject index e &&
                 selectors s constructor subject (index + 1) rest

let rec lemma_selector_index (s:S.checked_schema) (constructor:func_decl)
                             (subject:expr) (index:nat) (es:list expr) (n:nat)
  : Lemma (requires selectors s constructor subject index es /\ n < L.length es)
          (ensures selector_of s constructor subject (index + n) (L.index es n))
          (decreases es) =
  match es with
  | [] -> ()
  | _ :: rest -> if n > 0 then lemma_selector_index s constructor subject (index + 1) rest (n - 1)

let lemma_selector_value (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                         (constructor:func_decl) (subject:expr) (index:nat) (e:expr)
  : Lemma (requires D.scoped [] subject /\ D.scoped [] e /\
                    V.recognize constructor (T.evaluate s bc eq other subject) /\
                    selector_of s constructor subject index e)
          (ensures index < L.length (V.fields (T.evaluate s bc eq other subject)) /\
                   T.evaluate s bc eq other e ==
                   L.index (V.fields (T.evaluate s bc eq other subject)) index) =
  match e with
  | App f [_] ->
    let r = Some?.v (S.find_accessor f s.cases) in
    lemma_accessor_dispatch s f;
    S.lemma_signature_member s.cases r.matched_case;
    V.lemma_reconstruct (S.signature s) constructor (T.evaluate s bc eq other subject);
    V.lemma_fields_index (S.signature s) constructor.domain
      (V.fields (T.evaluate s bc eq other subject)) index
  | _ -> ()

let rebuild (s:S.checked_schema) (constructor:func_decl) (subject:expr) (candidate:expr) : bool =
  match candidate with
  | App f args ->
    f = constructor && L.mem f (S.signature s) &&
    L.length args = L.length f.domain && selectors s f subject 0 args
  | _ -> false

let lemma_rebuild (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                  (constructor:func_decl) (subject candidate:expr)
  : Lemma (requires D.scoped [] subject /\ D.scoped [] candidate /\
                    V.recognize constructor (T.evaluate s bc eq other subject) /\
                    rebuild s constructor subject candidate)
          (ensures T.evaluate s bc eq other candidate == T.evaluate s bc eq other subject) =
  match candidate with
  | App _ args ->
    let v = T.evaluate s bc eq other subject in
    let xs = T.evaluate_arguments s bc eq other args constructor.domain in
    V.lemma_reconstruct (S.signature s) constructor v;
    V.lemma_fields_length (S.signature s) constructor.domain xs;
    V.lemma_fields_length (S.signature s) constructor.domain (V.fields v);
    let at (n:nat)
      : Lemma (n < L.length xs ==> L.index xs n == L.index (V.fields v) n) =
      if n < L.length xs then (
        lemma_arguments_index s bc eq other args constructor.domain n;
        lemma_selector_index s constructor subject 0 args n;
        lemma_selector_value s bc eq other constructor subject n (L.index args n)) in
    FStar.Classical.forall_intro at;
    FStar.List.Tot.Properties.index_extensionality xs (V.fields v)
  | _ -> ()

let reconstruction (s:S.checked_schema) (guard conclusion:expr) : bool =
  match guard, conclusion with
  | App tester [subject], App equality [a; b] ->
    equality = R.eq_decl (get_sort subject) &&
    (match S.find_recognizer tester s.cases with
     | Some c ->
       (a = subject && rebuild s c.constructor subject b) ||
       (b = subject && rebuild s c.constructor subject a)
     | None -> false)
  | _, _ -> false

let lemma_reconstruction (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                         (guard conclusion:expr)
  : Lemma (requires D.scoped [] guard /\ D.scoped [] conclusion /\
                    reconstruction s guard conclusion /\ T.truth s bc eq other guard)
          (ensures T.truth s bc eq other conclusion) =
  match guard, conclusion with
  | App tester [subject], App _ [a; b] ->
    let c = Some?.v (S.find_recognizer tester s.cases) in
    lemma_recognizer s bc eq other tester subject;
    if a = subject then lemma_rebuild s bc eq other c.constructor subject b
    else lemma_rebuild s bc eq other c.constructor subject a;
    V.lemma_sort_eq (get_sort a) (get_sort b);
    T.lemma_equality s bc eq other a b
  | _, _ -> ()

let reconstruction_pair (s:S.checked_schema) (negative conclusion:expr) : bool =
  match negative with
  | App negation [guard] -> T.classify negation = T.Negation && reconstruction s guard conclusion
  | _ -> false

let guarded_reconstruction (s:S.checked_schema) (e:expr) : bool =
  match e with
  | App disjunction [a; b] ->
    T.classify disjunction = T.Nary B.Or &&
    (reconstruction_pair s a b || reconstruction_pair s b a)
  | _ -> false

let lemma_reconstruction_pair (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                              (negative conclusion:expr)
  : Lemma (requires D.scoped [] negative /\ D.scoped [] conclusion /\
                    reconstruction_pair s negative conclusion)
          (ensures T.truth s bc eq other negative || T.truth s bc eq other conclusion) =
  match negative with
  | App negation [guard] ->
    T.lemma_negation s bc eq other negation guard;
    if T.truth s bc eq other guard then lemma_reconstruction s bc eq other guard conclusion
  | _ -> ()

let lemma_guarded_reconstruction (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                 (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                                 (e:expr)
  : Lemma (requires D.scoped [] e /\ guarded_reconstruction s e)
          (ensures T.truth s bc eq other e) =
  match e with
  | App disjunction [a; b] ->
    T.lemma_nary s bc eq other disjunction [a; b] B.Or;
    if reconstruction_pair s a b then lemma_reconstruction_pair s bc eq other a b
    else lemma_reconstruction_pair s bc eq other b a
  | _ -> ()

let symmetric_equality (e:expr) : bool =
  match e with
  | App f [App g [a; b]; App h [c; d]] ->
    f = R.eq_decl bool_sort && g = R.eq_decl (get_sort a) && h = g && a = d && b = c
  | _ -> false

let lemma_symmetric_equality (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                             (e:expr)
  : Lemma (requires D.scoped [] e /\ symmetric_equality e)
          (ensures T.truth s bc eq other e) =
  match e with
  | App _ [App _ [a; b]; App _ [_; _]] ->
    V.lemma_sort_eq (get_sort b) (get_sort a);
    T.lemma_equality s bc eq other a b;
    T.lemma_equality s bc eq other b a;
    T.lemma_boolean_equality s bc eq other (R.mk_eq_expr a b) (R.mk_eq_expr b a)
  | _ -> ()

let axiom (s:S.checked_schema) (e:expr) : bool =
  symmetric_equality e || exhaustive s e || guarded_reconstruction s e

let lemma_axiom (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                (e:expr)
  : Lemma (requires D.scoped [] e /\ axiom s e)
          (ensures T.truth s bc eq other e) =
  if symmetric_equality e then lemma_symmetric_equality s bc eq other e
  else if exhaustive s e then lemma_exhaustive s bc eq other e
  else lemma_guarded_reconstruction s bc eq other e

let formula (s:S.checked_schema) (axioms:bool) (e:expr) : option B.skeleton =
  if get_sort e <> bool_sort then None
  else match normalize s 64 e with
  | None -> None
  | Some result -> Some (if axioms && axiom s result then B.Bool true else T.cut 64 result)

let lemma_formula (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                  (axioms:bool) (e:expr) (f:B.skeleton)
  : Lemma (requires D.scoped [] e /\ formula s axioms e == Some f)
          (ensures B.eval (T.truth s bc eq other) f == T.truth s bc eq other e) =
  let result = Some?.v (normalize s 64 e) in
  lemma_normalize s bc eq other 64 e result;
  if axioms && axiom s result then lemma_axiom s bc eq other result
  else T.lemma_cut s bc eq other 64 result

let rec formulas (s:S.checked_schema) (es:list expr) : Tot (option (list B.skeleton)) (decreases es) =
  match es with
  | [] -> Some []
  | e :: rest ->
    (match formula s false e, formulas s rest with
     | Some f, Some fs -> Some (f :: fs)
     | _, _ -> None)

let rec lemma_formulas (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                       (es:list expr) (fs:list B.skeleton)
  : Lemma (requires D.scoped_args [] es /\ formulas s es == Some fs)
          (ensures B.eval_args (T.truth s bc eq other) B.And fs == T.truths s bc eq other es)
          (decreases es) =
  match es, fs with
  | e :: rest, f :: tail ->
    lemma_formula s bc eq other false e f;
    lemma_formulas s bc eq other rest tail
  | _, _ -> ()

let propositional (f:B.skeleton) : bool =
  let simplified = N.normalize false f in
  if simplified = B.Bool true then true
  else if N.clause_tautology simplified || N.equivalent f (B.Bool true) then true
  else
    let atoms = B.unique (B.support simplified) in
    L.length atoms <= 12 && B.check_rows atoms (fun _ -> false) simplified (B.Bool true)

let lemma_propositional (rho:expr -> bool) (f:B.skeleton)
  : Lemma (requires propositional f) (ensures B.eval rho f) =
  let simplified = N.normalize false f in
  N.lemma_normalize_sound rho false f;
  if simplified = B.Bool true then ()
  else if N.clause_tautology simplified then N.lemma_clause_tautology_sound rho simplified
  else if N.equivalent f (B.Bool true) then N.lemma_equivalent_sound rho f (B.Bool true)
  else (
    B.lemma_unique_mem (B.support simplified);
    B.lemma_check_rows_sound (B.unique (B.support simplified)) (fun _ -> false)
      rho simplified (B.Bool true))

let rec lemma_true_member (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                          (facts:list expr) (e:expr)
  : Lemma (requires T.truths s bc eq other facts /\ L.mem e facts)
          (ensures T.truth s bc eq other e)
          (decreases facts) =
  match facts with [] -> () | f :: rest -> if f <> e then lemma_true_member s bc eq other rest e

let literals (e:expr) : list expr =
  if e = R.false_expr then []
  else match e with
  | App f es -> if T.classify f = T.Nary B.Or then es else [e]
  | _ -> [e]

let eliminated (units:list expr) (e:expr) : bool =
  L.mem (R.mk_not_expr e) units ||
  (match e with
   | App f [a] -> T.classify f = T.Negation && L.mem a units
   | _ -> false)

let rec resolved (units:list expr) (conclusion:expr) (clause:list expr)
  : Tot bool (decreases clause) =
  match clause with
  | [] -> true
  | e :: rest ->
    (eliminated units e || e = conclusion || L.mem e (literals conclusion)) &&
    resolved units conclusion rest

let simple_consequence (facts:list expr) (conclusion:expr) : bool =
  L.mem conclusion facts ||
  (match facts with
   | [a; App f [source; target]] ->
     a = source && conclusion = target &&
     (T.classify f = T.Equality bool_sort || T.classify f = T.Implication)
   | _ -> false) ||
  (match facts with
   | [] -> false
   | c :: units -> resolved units conclusion (literals c))

let lemma_literals (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                   (e:expr)
  : Lemma (requires D.scoped [] e /\ get_sort e == bool_sort)
          (ensures B.eval_args (T.truth s bc eq other) B.Or (L.map B.Atom (literals e)) ==
                   T.truth s bc eq other e) =
  if e = R.false_expr then T.lemma_cut s bc eq other 1 e
  else match e with
  | App f es -> if T.classify f = T.Nary B.Or then T.lemma_nary s bc eq other f es B.Or
  | _ -> ()

let lemma_eliminated (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                     (units:list expr) (e:expr)
  : Lemma (requires T.truths s bc eq other units /\ eliminated units e /\ T.truth s bc eq other e)
          (ensures False) =
  if L.mem (R.mk_not_expr e) units then (
    lemma_true_member s bc eq other units (R.mk_not_expr e);
    T.lemma_negation s bc eq other R.not_decl e)
  else match e with
  | App f [a] ->
    lemma_true_member s bc eq other units a;
    T.lemma_negation s bc eq other f a
  | _ -> ()

let rec lemma_literal_member (rho:expr -> bool) (es:list expr) (e:expr)
  : Lemma (requires L.mem e es /\ rho e)
          (ensures B.eval_args rho B.Or (L.map B.Atom es))
          (decreases es) =
  match es with [] -> () | x :: rest -> if x <> e then lemma_literal_member rho rest e

let rec lemma_resolved (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                      (units:list expr) (conclusion:expr) (clause:list expr)
  : Lemma (requires T.truths s bc eq other units /\ D.scoped [] conclusion /\
                    get_sort conclusion == bool_sort /\ resolved units conclusion clause /\
                    B.eval_args (T.truth s bc eq other) B.Or (L.map B.Atom clause))
          (ensures T.truth s bc eq other conclusion)
          (decreases clause) =
  match clause with
  | [] -> ()
  | e :: rest ->
    if T.truth s bc eq other e then (
      if eliminated units e then lemma_eliminated s bc eq other units e
      else if e <> conclusion then (
        lemma_literal_member (T.truth s bc eq other) (literals conclusion) e;
        lemma_literals s bc eq other conclusion))
    else lemma_resolved s bc eq other units conclusion rest

let lemma_simple_consequence (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                             (facts:list expr) (conclusion:expr)
  : Lemma (requires T.truths s bc eq other facts /\ D.scoped [] conclusion /\
                    get_sort conclusion == bool_sort /\ simple_consequence facts conclusion)
          (ensures T.truth s bc eq other conclusion) =
  if L.mem conclusion facts then lemma_true_member s bc eq other facts conclusion
  else
    let mp =
      match facts with
      | [a; App f [source; target]] ->
        a = source && conclusion = target &&
        (T.classify f = T.Equality bool_sort || T.classify f = T.Implication)
      | _ -> false in
    if mp then (
      match facts with
      | [a; App f [source; target]] ->
        if T.classify f = T.Equality bool_sort then
          T.lemma_boolean_equality s bc eq other source target
        else T.lemma_evaluate_core s bc eq other f [source; target]
      | _ -> ())
    else match facts with
    | [] -> ()
    | c :: units ->
      lemma_literals s bc eq other c;
      lemma_resolved s bc eq other units conclusion (literals c)

let rec shared_boundaries (depth:nat) (es:list expr) : Tot (list expr) (decreases es) =
  match es with
  | [] -> []
  | e :: rest ->
    L.append (B.intersect (BR.boolean_nodes depth e) (BR.boolean_nodes_args depth rest))
      (shared_boundaries depth rest)

let reflection_boundaries (depth:nat) (facts:list expr) (conclusion:expr) : list expr =
  let common = shared_boundaries depth (conclusion :: facts) in
  B.unique (L.append common
    (match conclusion with
     | App f [a; b] ->
       if T.classify f = T.Equality bool_sort then
         B.intersect (BR.boolean_nodes depth a) (BR.boolean_nodes depth b)
       else []
     | _ -> []))

let boolean_consequence_at (depth:nat) (facts:list expr) (conclusion:expr) : bool =
  let premise = App (BR.connective_decl BR.Conjunction facts) facts in
  let boundaries = reflection_boundaries depth facts conclusion in
  propositional (B.Implies (T.cut_with_boundaries boundaries depth premise)
                          (T.cut_with_boundaries boundaries depth conclusion))

let boolean_consequence (facts:list expr) (conclusion:expr) : bool =
  boolean_consequence_at 2 facts conclusion ||
  boolean_consequence_at 4 facts conclusion ||
  boolean_consequence_at 8 facts conclusion

let lemma_boolean_consequence_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                 (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                                 (depth:nat) (facts:list expr) (conclusion:expr)
  : Lemma (requires T.truths s bc eq other facts /\ D.scoped [] conclusion /\
                    get_sort conclusion == bool_sort /\ boolean_consequence_at depth facts conclusion)
          (ensures T.truth s bc eq other conclusion) =
  let rec sorted (es:list expr)
    : Lemma (requires T.truths s bc eq other es)
            (ensures D.scoped_args [] es /\
                     (forall (e:expr). L.mem e es ==> get_sort e == bool_sort))
            (decreases es) =
    match es with [] -> () | _ :: rest -> sorted rest in
  sorted facts;
  lemma_boolean_domain facts;
  lemma_conjunction s bc eq other facts;
  T.lemma_truths s bc eq other facts;
  let premise = App (BR.connective_decl BR.Conjunction facts) facts in
  let boundaries = reflection_boundaries depth facts conclusion in
  T.lemma_cut_with_boundaries s bc eq other boundaries depth premise;
  T.lemma_cut_with_boundaries s bc eq other boundaries depth conclusion;
  lemma_propositional (T.truth s bc eq other)
    (B.Implies (T.cut_with_boundaries boundaries depth premise)
               (T.cut_with_boundaries boundaries depth conclusion))

let lemma_boolean_consequence (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                              (facts:list expr) (conclusion:expr)
  : Lemma (requires T.truths s bc eq other facts /\ D.scoped [] conclusion /\
                    get_sort conclusion == bool_sort /\ boolean_consequence facts conclusion)
          (ensures T.truth s bc eq other conclusion) =
  if boolean_consequence_at 2 facts conclusion then
    lemma_boolean_consequence_at s bc eq other 2 facts conclusion
  else if boolean_consequence_at 4 facts conclusion then
    lemma_boolean_consequence_at s bc eq other 4 facts conclusion
  else lemma_boolean_consequence_at s bc eq other 8 facts conclusion

let rec reconstruction_from (s:S.checked_schema) (facts:list expr) (conclusion:expr)
  : Tot bool (decreases facts) =
  match facts with
  | [] -> false
  | f :: rest -> reconstruction s f conclusion || reconstruction_from s rest conclusion

let rec lemma_reconstruction_from (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                  (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                                  (facts:list expr) (conclusion:expr)
  : Lemma (requires D.scoped_args [] facts /\ D.scoped [] conclusion /\
                    T.truths s bc eq other facts /\ reconstruction_from s facts conclusion)
          (ensures T.truth s bc eq other conclusion)
          (decreases facts) =
  match facts with
  | [] -> ()
  | f :: rest ->
    if reconstruction s f conclusion then lemma_reconstruction s bc eq other f conclusion
    else lemma_reconstruction_from s bc eq other rest conclusion

let rec excluded_atoms (facts:list expr) : Tot (list expr) (decreases facts) =
  match facts with
  | [] -> []
  | App f [a] :: rest ->
    if T.classify f = T.Negation then a :: excluded_atoms rest else excluded_atoms rest
  | _ :: rest -> excluded_atoms rest

let exclusion_clause (facts:list expr) (conclusion:expr) : expr =
  let es = conclusion :: excluded_atoms facts in
  App (BR.connective_decl BR.Disjunction es) es

let exhaustiveness_from (s:S.checked_schema) (facts:list expr) (conclusion:expr) : bool =
  match conclusion with
  | App f [_] ->
    Some? (S.find_recognizer f s.cases) &&
    D.scoped [] (exclusion_clause facts conclusion) && exhaustive s (exclusion_clause facts conclusion)
  | _ -> false

let rec lemma_excluded_atoms (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                             (facts:list expr)
  : Lemma (requires T.truths s bc eq other facts)
          (ensures not (B.eval_args (T.truth s bc eq other) B.Or (L.map B.Atom (excluded_atoms facts))))
          (decreases facts) =
  match facts with
  | [] -> ()
  | App f [a] :: rest ->
    lemma_excluded_atoms s bc eq other rest;
    if T.classify f = T.Negation then T.lemma_negation s bc eq other f a
  | _ :: rest -> lemma_excluded_atoms s bc eq other rest

let lemma_exhaustiveness_from (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                              (facts:list expr) (conclusion:expr)
  : Lemma (requires T.truths s bc eq other facts /\ exhaustiveness_from s facts conclusion)
          (ensures T.truth s bc eq other conclusion) =
  let es = conclusion :: excluded_atoms facts in
  lemma_exhaustive s bc eq other (exclusion_clause facts conclusion);
  lemma_excluded_atoms s bc eq other facts;
  T.lemma_nary s bc eq other (BR.connective_decl BR.Disjunction es) es B.Or

let transport_exclusion (s:S.checked_schema) (equation fact:expr) : option expr =
  match equation, fact with
  | App equality [a; b], App negation [App recognizer [subject]] ->
    if equality = R.eq_decl (get_sort a) && T.classify negation = T.Negation &&
       Some? (S.find_recognizer recognizer s.cases) && (subject = a || subject = b) then
      let target = if subject = a then b else a in
      let result = App negation [App recognizer [target]] in
      if D.scoped [] result then Some result else None
    else None
  | _, _ -> None

let lemma_transport_exclusion (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                              (equation fact result:expr)
  : Lemma (requires T.truth s bc eq other equation /\ T.truth s bc eq other fact /\
                    transport_exclusion s equation fact == Some result)
          (ensures T.truth s bc eq other result) =
  match equation, fact with
  | App _ [a; b], App negation [App recognizer [subject]] ->
    V.lemma_sort_eq (get_sort b) (get_sort a);
    T.lemma_equality s bc eq other a b;
    let target = if subject = a then b else a in
    T.lemma_negation s bc eq other negation (App recognizer [subject]);
    T.lemma_negation s bc eq other negation (App recognizer [target]);
    lemma_recognizer s bc eq other recognizer subject;
    lemma_recognizer s bc eq other recognizer target
  | _, _ -> ()

let rec transport_exclusions (s:S.checked_schema) (equation:expr) (facts:list expr)
  : Tot (list expr) (decreases facts) =
  match facts with
  | [] -> []
  | fact :: rest ->
    let tail = transport_exclusions s equation rest in
    match transport_exclusion s equation fact with
    | Some result -> result :: tail
    | None -> tail

let rec lemma_transport_exclusions (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                   (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                                   (equation:expr) (facts:list expr)
  : Lemma (requires T.truth s bc eq other equation /\ T.truths s bc eq other facts)
          (ensures T.truths s bc eq other (transport_exclusions s equation facts))
          (decreases facts) =
  match facts with
  | [] -> ()
  | fact :: rest ->
    lemma_transport_exclusions s bc eq other equation rest;
    match transport_exclusion s equation fact with
    | Some result -> lemma_transport_exclusion s bc eq other equation fact result
    | None -> ()

let rec equality_exclusions (s:S.checked_schema) (equations facts:list expr)
  : Tot (list expr) (decreases equations) =
  match equations with
  | [] -> facts
  | equation :: rest ->
    L.append (transport_exclusions s equation facts) (equality_exclusions s rest facts)

let rec lemma_truths_append (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                            (xs ys:list expr)
  : Lemma (requires T.truths s bc eq other xs /\ T.truths s bc eq other ys)
          (ensures T.truths s bc eq other (L.append xs ys))
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_truths_append s bc eq other rest ys

let rec lemma_equality_exclusions (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                 (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                                 (equations facts:list expr)
  : Lemma (requires T.truths s bc eq other equations /\ T.truths s bc eq other facts)
          (ensures T.truths s bc eq other (equality_exclusions s equations facts))
          (decreases equations) =
  match equations with
  | [] -> ()
  | equation :: rest ->
    lemma_transport_exclusions s bc eq other equation facts;
    lemma_equality_exclusions s bc eq other rest facts;
    lemma_truths_append s bc eq other
      (transport_exclusions s equation facts) (equality_exclusions s rest facts)

let normalized_consequence (s:S.checked_schema) (facts:list expr) (conclusion:expr) : bool =
  match formulas s facts, formula s true conclusion with
  | Some fs, Some c -> propositional (B.Implies (B.Nary B.And fs) c)
  | _, _ -> false

let lemma_normalized_consequence (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                 (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                                 (facts:list expr) (conclusion:expr)
  : Lemma (requires T.truths s bc eq other facts /\ D.scoped_args [] facts /\
                    D.scoped [] conclusion /\ normalized_consequence s facts conclusion)
          (ensures T.truth s bc eq other conclusion) =
  let fs = Some?.v (formulas s facts) in
  let c = Some?.v (formula s true conclusion) in
  lemma_formulas s bc eq other facts fs;
  lemma_formula s bc eq other true conclusion c;
  lemma_propositional (T.truth s bc eq other) (B.Implies (B.Nary B.And fs) c)

let equality_consequence (s:S.checked_schema) (facts:list expr) (conclusion:expr) : bool =
  let expanded = equality_exclusions s facts facts in
  D.scoped_args [] expanded &&
  (exhaustiveness_from s expanded conclusion || normalized_consequence s expanded conclusion)

let lemma_equality_consequence (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                               (facts:list expr) (conclusion:expr)
  : Lemma (requires T.truths s bc eq other facts /\ D.scoped [] conclusion /\
                    equality_consequence s facts conclusion)
          (ensures T.truth s bc eq other conclusion) =
  let expanded = equality_exclusions s facts facts in
  lemma_equality_exclusions s bc eq other facts facts;
  if exhaustiveness_from s expanded conclusion then
    lemma_exhaustiveness_from s bc eq other expanded conclusion
  else lemma_normalized_consequence s bc eq other expanded conclusion

let consequence (s:S.checked_schema) (facts:list expr) (conclusion:expr) : bool =
  D.scoped_args [] facts && D.scoped [] conclusion && get_sort conclusion = bool_sort &&
  (axiom s conclusion || simple_consequence facts conclusion || boolean_consequence facts conclusion ||
   reconstruction_from s facts conclusion || exhaustiveness_from s facts conclusion ||
   normalized_consequence s facts conclusion || equality_consequence s facts conclusion)

let lemma_consequence (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                      (facts:list expr) (conclusion:expr)
  : Lemma (requires T.truths s bc eq other facts /\ consequence s facts conclusion)
          (ensures T.truth s bc eq other conclusion) =
  if axiom s conclusion then lemma_axiom s bc eq other conclusion
  else if simple_consequence facts conclusion then lemma_simple_consequence s bc eq other facts conclusion
  else if boolean_consequence facts conclusion then
    lemma_boolean_consequence s bc eq other facts conclusion
  else if reconstruction_from s facts conclusion then
    lemma_reconstruction_from s bc eq other facts conclusion
  else if exhaustiveness_from s facts conclusion then
    lemma_exhaustiveness_from s bc eq other facts conclusion
  else if normalized_consequence s facts conclusion then
    lemma_normalized_consequence s bc eq other facts conclusion
  else lemma_equality_consequence s bc eq other facts conclusion
