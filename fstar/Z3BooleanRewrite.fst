module Z3BooleanRewrite

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open FStar.List.Tot
module B = Z3BoundedBoolEquiv
module N = Z3BooleanNormalForm
module C = Z3CanonicalOps

type connective =
  | Conjunction
  | Disjunction

let rec boolean_domain (args:list expr) : Tot (list sort) (decreases args) =
  match args with
  | [] -> []
  | _ :: rest -> bool_sort :: boolean_domain rest

let rec boolean_args (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest -> get_sort a = bool_sort && boolean_args rest

let connective_decl (op:connective) (args:list expr) : func_decl =
  { decl_name = (if op = Conjunction then "and" else "or");
    domain = boolean_domain args;
    range = bool_sort;
    interp = Some (if op = Conjunction then op_and else op_or);
    int_params = [] }

let rec lemma_boolean_domain (args:list expr)
  : Lemma (ensures C.boolean_sorts (boolean_domain args)) (decreases args)
  = match args with
    | [] -> ()
    | _ :: rest -> lemma_boolean_domain rest

(* The connective declarations built here are the canonical `and`/`or`. *)
let lemma_connective_decl (op:connective) (args:list expr)
  : Lemma (ensures (op = Conjunction ==> C.canonical_and (connective_decl op args)) /\
                   (op = Disjunction ==> C.canonical_or (connective_decl op args)))
          [SMTPat (connective_decl op args)]
  = lemma_boolean_domain args

let connective_app (op:connective) (f:func_decl) (args:list expr) : bool =
  f = connective_decl op args && boolean_args args

let lemma_connective_app (op:connective) (f:func_decl) (args:list expr)
  : Lemma (requires connective_app op f args)
          (ensures (op = Conjunction ==> C.canonical_and f) /\ (op = Disjunction ==> C.canonical_or f))
          [SMTPat (connective_app op f args)]
  = lemma_boolean_domain args

let rec flatten_expr (op:connective) (e:expr)
  : Tot (list expr) (decreases e) =
  match e with
  | App f args ->
    if connective_app op f args then flatten_args op args else [e]
  | _ -> [e]

and flatten_args (op:connective) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> flatten_expr op a @ flatten_args op rest

let flatten_rewrite (e:expr) : option expr =
  match e with
  | App f args ->
    let op = if f.decl_name = "and" then Conjunction else Disjunction in
    if connective_app op f args then
      let flat = flatten_args op args in
      Some (App (connective_decl op flat) flat)
    else None
  | _ -> None

let connective_holds (op:connective) (i:interpretation value) (rho:env value)
                     (args:list expr) : prop =
  match op with
  | Conjunction -> conj_holds i rho args
  | Disjunction -> clause_holds i rho args

(* The canonical connective built here holds exactly when its arguments do. *)
let lemma_connective_holds (op:connective) (i:interpretation value) (rho:env value) (args:list expr)
  : Lemma (requires and_sound i /\ or_sound i)
          (ensures lit_true i rho (App (connective_decl op args) args) <==> connective_holds op i rho args)
  = lemma_connective_decl op args

let rec lemma_connective_append (op:connective) (i:interpretation value)
                                 (rho:env value) (xs ys:list expr)
  : Lemma
      (connective_holds op i rho (xs @ ys) <==>
       (if op = Conjunction
        then connective_holds op i rho xs /\ connective_holds op i rho ys
        else connective_holds op i rho xs \/ connective_holds op i rho ys))
      (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: rest -> lemma_connective_append op i rho rest ys

let rec lemma_flatten_expr_sound (op:connective) (i:interpretation value)
                                 (rho:env value) (e:expr)
  : Lemma (requires and_sound i /\ or_sound i)
          (ensures connective_holds op i rho (flatten_expr op e) <==> lit_true i rho e)
          (decreases e)
  = match e with
    | App f args ->
      if connective_app op f args then (
        lemma_flatten_args_sound op i rho args;
        match op with Conjunction | Disjunction -> ())
    | _ -> ()

and lemma_flatten_args_sound (op:connective) (i:interpretation value)
                             (rho:env value) (args:list expr)
  : Lemma (requires and_sound i /\ or_sound i)
          (ensures connective_holds op i rho (flatten_args op args) <==>
                   connective_holds op i rho args)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      lemma_flatten_expr_sound op i rho a;
      lemma_flatten_args_sound op i rho rest;
      lemma_connective_append op i rho (flatten_expr op a) (flatten_args op rest)

let lemma_flatten_rewrite_sound (i:interpretation value) (rho:env value) (s t:expr)
  : Lemma (requires boolean_model i /\ and_sound i /\ or_sound i /\
                    flatten_rewrite s == Some t)
          (ensures eval i s rho == eval i t rho)
  = match s with
    | App f args ->
      let op = if f.decl_name = "and" then Conjunction else Disjunction in
      lemma_flatten_args_sound op i rho args;
      (match op with Conjunction | Disjunction -> ());
      (match eval i s rho, eval i t rho with
       | VBool _, VBool _ -> ()
       | _, _ -> ())
    | _ -> ()

let boolean_ite_decl : func_decl =
  { decl_name = "if"; domain = [bool_sort; bool_sort; bool_sort];
    range = bool_sort; interp = Some op_ite; int_params = [] }

let boolean_xor_decl : func_decl =
  { decl_name = "xor"; domain = [bool_sort; bool_sort];
    range = bool_sort; interp = Some op_xor; int_params = [] }

let native_bool_op (f:func_decl) (args:list expr) : B.bool_op =
  if not (boolean_args args) then B.Opaque
  else if connective_app Conjunction f args then B.BNary B.And
  else if connective_app Disjunction f args then B.BNary B.Or
  else if f = { decl_name = "not"; domain = [bool_sort]; range = bool_sort;
                interp = Some op_not; int_params = [] } && length args = 1
  then B.BNot
  else if (f.decl_name = "=>" || f.decl_name = "implies") &&
          f.domain = [bool_sort; bool_sort] && f.range = bool_sort &&
          f.interp = Some op_implies && f.int_params = [] && length args = 2
  then B.BImplies
  else if f = boolean_ite_decl && length args = 3 then B.BIte
  else if f = boolean_xor_decl && length args = 2 then B.BNary B.Xor
  else if f = eq_decl bool_sort && length args = 2 then B.BEq
  else if f = { decl_name = "true"; domain = []; range = bool_sort;
                interp = Some op_true; int_params = [] } && args = []
  then B.BTrue
  else if f = { decl_name = "false"; domain = []; range = bool_sort;
                interp = Some op_false; int_params = [] } && args = []
  then B.BFalse
  else B.Opaque

(* The declarations `native_bool_op` recognizes are the canonical connectives. *)
let lemma_native_bool_op (f:func_decl) (args:list expr)
  : Lemma (match native_bool_op f args with
           | B.BNary B.And -> C.canonical_and f
           | B.BNary B.Or -> C.canonical_or f
           | B.BNot -> C.canonical_not f
           | B.BImplies -> C.canonical_implies f
           | B.BEq -> C.canonical_eq f
           | B.BTrue -> C.canonical_true f
           | B.BFalse -> C.canonical_false f
           | _ -> True)
  = lemma_boolean_domain args

let reflexive_equality (e:expr) : bool =
  match e with
  | App f [a; b] -> f = eq_decl (get_sort a) && a = b
  | _ -> false

let rec boolean_nodes (depth:nat) (e:expr) : Tot (list expr) (decreases e) =
  match e with
  | App f args ->
    (match native_bool_op f args with
     | B.BTrue | B.BFalse -> []
     | B.Opaque -> [e]
     | _ -> e :: (if depth = 0 then [] else boolean_nodes_args (depth - 1) args))
  | _ -> [e]

and boolean_nodes_args (depth:nat) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> boolean_nodes depth a @ boolean_nodes_args depth rest

let boolean_leaf (e:expr) : bool =
  match e with
  | App f args ->
    (match native_bool_op f args with B.BTrue | B.BFalse | B.Opaque -> true | _ -> false)
  | _ -> true

let rec boolean_leaves (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest -> boolean_leaf a && boolean_leaves rest

let rec boolean_frontier (depth:nat) (e:expr) : Tot (list expr) (decreases e) =
  match e with
  | App f args ->
    (match native_bool_op f args with
     | B.BTrue | B.BFalse | B.Opaque -> []
     | _ -> if depth = 0 then (if boolean_leaves args then [] else [e])
            else boolean_args_frontier (depth - 1) args)
  | _ -> []

and boolean_args_frontier (depth:nat) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> boolean_frontier depth a @ boolean_args_frontier depth rest

let rec boolean_cut (boundaries:list expr) (depth:nat) (e:expr)
  : Tot B.skeleton (decreases e) =
  if reflexive_equality e then B.Bool true
  else if mem e boundaries then B.Atom e
  else match e with
  | App f args ->
    (match native_bool_op f args with
     | B.BTrue -> B.Bool true
     | B.BFalse -> B.Bool false
     | B.BNary op ->
       if depth = 0 then B.Atom e
       else B.Nary op (boolean_cut_args boundaries (depth - 1) args)
     | B.BNot ->
       (match args with
        | [a] -> if depth = 0 then B.Atom e
                 else B.Not (boolean_cut boundaries (depth - 1) a)
        | _ -> B.Atom e)
     | B.BImplies ->
       (match args with
        | [a; b] -> if depth = 0 then B.Atom e
                    else B.Implies (boolean_cut boundaries (depth - 1) a)
                                   (boolean_cut boundaries (depth - 1) b)
        | _ -> B.Atom e)
     | B.BEq ->
       (match args with
        | [a; b] -> if depth = 0 then B.Atom e
                    else B.Eq (boolean_cut boundaries (depth - 1) a)
                              (boolean_cut boundaries (depth - 1) b)
        | _ -> B.Atom e)
     | B.BIte ->
       (match args with
        | [c; t; f] -> if depth = 0 then B.Atom e
                       else B.boolean_ite (boolean_cut boundaries (depth - 1) c)
                                          (boolean_cut boundaries (depth - 1) t)
                                          (boolean_cut boundaries (depth - 1) f)
        | _ -> B.Atom e)
     | _ -> B.Atom e)
  | _ -> B.Atom e

and boolean_cut_args (boundaries:list expr) (depth:nat) (args:list expr)
  : Tot (list B.skeleton) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> boolean_cut boundaries depth a :: boolean_cut_args boundaries depth rest

let rec boolean_height (e:expr) : Tot nat (decreases e) =
  match e with
  | App f args -> if native_bool_op f args = B.Opaque then 0
                  else 1 + boolean_args_height args
  | _ -> 0

and boolean_args_height (args:list expr) : Tot nat (decreases args) =
  match args with
  | [] -> 0
  | a :: rest ->
    let x = boolean_height a in
    let y = boolean_args_height rest in
    if x > y then x else y

let structural_boolean_equiv (s t:expr) : bool =
  N.equivalent (boolean_cut [] (boolean_height s) s)
               (boolean_cut [] (boolean_height t) t)

let boolean_equiv (depth width:nat) (s t:expr) : bool =
  if get_sort s <> bool_sort || get_sort t <> bool_sort then false
  else if structural_boolean_equiv s t then true
  else
    let boundaries = B.unique (B.intersect (boolean_nodes depth s) (boolean_nodes depth t)) in
    let cs = boolean_cut boundaries depth s in
    let ct = boolean_cut boundaries depth t in
    let atoms = B.unique (B.support cs @ B.support ct) in
    N.equivalent cs ct ||
    (length atoms <= width && B.check_rows atoms (fun _ -> false) cs ct)

let bool_value (v:value) : bool =
  match v with VBool b -> b | _ -> false

let valuation (i:interpretation value) (rho:env value) : expr -> bool =
  fun e -> bool_value (eval i e rho)

let ite_sound (i:interpretation value) : prop =
  forall (c t e:expr) (rho:env value).
    {:pattern (eval i (App boolean_ite_decl [c; t; e]) rho)}
    boolean_args [c; t; e] ==>
    eval i (App boolean_ite_decl [c; t; e]) rho ==
      (if bool_value (eval i c rho) then eval i t rho else eval i e rho)

let xor_sound (i:interpretation value) : prop =
  forall (a b:expr) (rho:env value).
    {:pattern (eval i (App boolean_xor_decl [a; b]) rho)}
    boolean_args [a; b] ==>
    eval i (App boolean_xor_decl [a; b]) rho ==
      VBool (bool_value (eval i a rho) <> bool_value (eval i b rho))

let boolean_rewrite_model (i:interpretation value) : prop =
  boolean_model i /\ not_sound i /\ and_sound i /\ or_sound i /\
  implies_sound i /\ eq_sound i /\ true_sound i /\ false_sound i /\ ite_sound i /\ xor_sound i

let rec lemma_boolean_cut_sound (boundaries:list expr) (depth:nat)
                                (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires boolean_rewrite_model i /\ get_sort e == bool_sort)
          (ensures B.eval (valuation i rho) (boolean_cut boundaries depth e) ==
                   bool_value (eval i e rho))
          (decreases e) =
  if reflexive_equality e then (
    match e with App _ [_; _] -> () | _ -> ())
  else if mem e boundaries then ()
  else match e with
  | App f args ->
    lemma_native_bool_op f args;
    (match native_bool_op f args with
     | B.BTrue | B.BFalse -> ()
     | B.BNary B.Xor ->
       (match args with
        | [a; b] ->
          if depth > 0 then (
            lemma_boolean_cut_sound boundaries (depth - 1) i rho a;
            lemma_boolean_cut_sound boundaries (depth - 1) i rho b)
        | _ -> ())
     | B.BNary op ->
       if depth > 0 then (
         lemma_boolean_cut_args_sound boundaries (depth - 1) i rho args;
         match op with B.And | B.Or | B.Xor -> ())
     | B.BNot ->
       (match args with
        | [a] ->
          if depth > 0 then (
            lemma_boolean_cut_sound boundaries (depth - 1) i rho a;
            match eval i a rho, eval i e rho with VBool _, VBool _ -> () | _, _ -> ())
        | _ -> ())
     | B.BImplies | B.BEq ->
       (match args with
        | [a; b] ->
          if depth > 0 then (
            lemma_boolean_cut_sound boundaries (depth - 1) i rho a;
            lemma_boolean_cut_sound boundaries (depth - 1) i rho b;
            match eval i a rho, eval i b rho, eval i e rho with
            | VBool _, VBool _, VBool _ -> () | _, _, _ -> ())
        | _ -> ())
     | B.BIte ->
       (match args with
        | [c; t; f] ->
          if depth > 0 then (
            lemma_boolean_cut_sound boundaries (depth - 1) i rho c;
            lemma_boolean_cut_sound boundaries (depth - 1) i rho t;
            lemma_boolean_cut_sound boundaries (depth - 1) i rho f;
            B.lemma_boolean_ite_eval (valuation i rho)
              (boolean_cut boundaries (depth - 1) c)
              (boolean_cut boundaries (depth - 1) t)
              (boolean_cut boundaries (depth - 1) f);
            match eval i c rho, eval i t rho, eval i f rho with
            | VBool _, VBool _, VBool _ -> () | _, _, _ -> ())
        | _ -> ())
     | _ -> ())
  | _ -> ()

and lemma_boolean_cut_args_sound (boundaries:list expr) (depth:nat)
                                 (i:interpretation value) (rho:env value) (args:list expr)
  : Lemma (requires boolean_rewrite_model i /\ boolean_args args)
          (ensures
            (B.eval_args (valuation i rho) B.And (boolean_cut_args boundaries depth args) == true
             <==> conj_holds i rho args) /\
            (B.eval_args (valuation i rho) B.Or (boolean_cut_args boundaries depth args) == true
             <==> clause_holds i rho args))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_boolean_cut_sound boundaries depth i rho a;
    lemma_boolean_cut_args_sound boundaries depth i rho rest;
    match eval i a rho with VBool _ -> () | _ -> ()

let lemma_boolean_equiv_sound (depth width:nat) (i:interpretation value)
                              (rho:env value) (s t:expr)
  : Lemma (requires boolean_rewrite_model i /\ boolean_equiv depth width s t)
          (ensures eval i s rho == eval i t rho) =
  let boundaries = B.unique (B.intersect (boolean_nodes depth s) (boolean_nodes depth t)) in
  let cs = boolean_cut boundaries depth s in
  let ct = boolean_cut boundaries depth t in
  let atoms = B.unique (B.support cs @ B.support ct) in
  if structural_boolean_equiv s t then (
    N.lemma_equivalent_sound (valuation i rho)
      (boolean_cut [] (boolean_height s) s) (boolean_cut [] (boolean_height t) t);
    lemma_boolean_cut_sound [] (boolean_height s) i rho s;
    lemma_boolean_cut_sound [] (boolean_height t) i rho t)
  else (
    if N.equivalent cs ct then N.lemma_equivalent_sound (valuation i rho) cs ct
    else (
      B.lemma_mem_append (B.support cs) (B.support ct);
      B.lemma_unique_mem (B.support cs @ B.support ct);
      assert (B.agree_outside atoms (fun _ -> false) (valuation i rho) cs ct);
      B.lemma_check_rows_sound atoms (fun _ -> false) (valuation i rho) cs ct);
    lemma_boolean_cut_sound boundaries depth i rho s;
    lemma_boolean_cut_sound boundaries depth i rho t);
  match eval i s rho, eval i t rho with VBool _, VBool _ -> () | _, _ -> ()

let boolean_search (s t:expr) : bool =
  get_sort s = bool_sort && get_sort t = bool_sort &&
  N.shannon 7 (N.normalize_context 2 (boolean_cut [] (boolean_height s) s))
              (N.normalize_context 2 (boolean_cut [] (boolean_height t) t))

let lemma_boolean_search_sound (i:interpretation value) (rho:env value) (s t:expr)
  : Lemma (requires boolean_rewrite_model i /\ boolean_search s t)
          (ensures eval i s rho == eval i t rho) =
  let cs = boolean_cut [] (boolean_height s) s in
  let ct = boolean_cut [] (boolean_height t) t in
  N.lemma_shannon_sound (valuation i rho) 7 (N.normalize_context 2 cs) (N.normalize_context 2 ct);
  N.lemma_normalize_context_sound (valuation i rho) 2 cs;
  N.lemma_normalize_context_sound (valuation i rho) 2 ct;
  lemma_boolean_cut_sound [] (boolean_height s) i rho s;
  lemma_boolean_cut_sound [] (boolean_height t) i rho t;
  match eval i s rho, eval i t rho with VBool _, VBool _ -> () | _, _ -> ()
