module Z3QuantifierReduce

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
module N = Z3QuantifierNnf
module P = Z3QuantifierPull
module S = Z3BinderSubstitution
module B = Z3BooleanRewrite
module L = FStar.List.Tot

let rec quantify_args (kind:quantifier_kind) (sorts:list sort) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | e :: rest -> Quantifier kind sorts bool_sort e :: quantify_args kind sorts rest

let push (e:expr) : option expr =
  match e with
  | Quantifier k bs s (App f args) ->
    if s = bool_sort && f.range = bool_sort && P.boolean_args args &&
       ((k = Forall_k && f.decl_name = "and") ||
        (k = Exists_k && f.decl_name = "or"))
    then Some (App f (quantify_args k bs args)) else None
  | _ -> None

let rec lemma_push_args (i:interpretation value) (rho:env value)
                        (kind:quantifier_kind) (sorts:list sort)
                        (f:func_decl) (args:list expr)
  : Lemma (requires N.quantifier_model i /\ boolean_model i /\ and_sound i /\ or_sound i /\
                    f.range = bool_sort /\ P.boolean_args args /\
                    ((kind = Forall_k /\ f.decl_name = "and") \/
                     (kind = Exists_k /\ f.decl_name = "or")))
          (ensures eval i (Quantifier kind sorts bool_sort (App f args)) rho ==
                   eval i (App f (quantify_args kind sorts args)) rho)
          (decreases args)
  = N.lemma_quantifier_truth i rho kind sorts (App f args);
    (match args with
     | [] -> ()
     | a :: rest ->
       N.lemma_quantifier_truth i rho kind sorts a;
       N.lemma_quantifier_truth i rho kind sorts (App f rest);
       let bodies (vs:list value{L.length vs = L.length sorts})
         : Lemma (lit_true i (shift vs rho) (App f args) <==>
                  (if kind = Forall_k
                   then lit_true i (shift vs rho) a /\ lit_true i (shift vs rho) (App f rest)
                   else lit_true i (shift vs rho) a \/ lit_true i (shift vs rho) (App f rest)))
         = () in
       FStar.Classical.forall_intro bodies;
       lemma_push_args i rho kind sorts f rest);
    match eval i (Quantifier kind sorts bool_sort (App f args)) rho,
          eval i (App f (quantify_args kind sorts args)) rho with
    | VBool _, VBool _ -> ()
    | _, _ -> ()

let lemma_push (i:interpretation value) (rho:env value) (e result:expr)
  : Lemma (requires N.quantifier_model i /\ boolean_model i /\ and_sound i /\ or_sound i /\
                    push e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | Quantifier k bs _ (App f args) -> lemma_push_args i rho k bs f args
    | _ -> ()

let normalize_root (e:expr) : option expr =
  match P.normalize 64 e with Some e' -> S.elim_unused e' | None -> None

let lemma_normalize_root (i:interpretation value) (rho:env value) (e result:expr)
  : Lemma (requires quant_extensional i /\ N.quantifier_model i /\ B.boolean_rewrite_model i /\
                    normalize_root e = Some result)
          (ensures eval i e rho == eval i result rho)
  = match P.normalize 64 e with
    | Some e' -> P.lemma_normalize_sound 64 i rho e e'; S.lemma_eliminate i rho e' result
    | None -> ()

let symmetric_equality (a b:expr) : bool =
  match a, b with
  | App f [x; y], App g [y'; x'] ->
    f = eq_decl (get_sort x) && g = f && get_sort x = get_sort y && x = x' && y = y'
  | _, _ -> false

let lemma_symmetric_equality (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires B.boolean_rewrite_model i /\ symmetric_equality a b)
          (ensures eval i a rho == eval i b rho)
  = match eval i a rho, eval i b rho with
    | VBool _, VBool _ -> ()
    | _, _ -> ()

let rec equivalent (fuel:nat) (a b:expr) : Tot bool (decreases %[fuel; a]) =
  if fuel = 0 then false
  else let next:nat = fuel - 1 in
  if a = b || symmetric_equality a b || B.boolean_equiv 8 10 a b then true
  else
  match normalize_root a, normalize_root b with
  | Some x, Some y ->
    x = y || symmetric_equality x y || B.boolean_equiv 8 10 x y ||
    (match x, y with
     | Quantifier k bs s body, Quantifier k' bs' s' body' ->
       k = k' && bs = bs' && s = s' && equivalent next body body'
     | App f args, App f' args' -> f = f' && equivalent_args next args args'
     | _, _ -> false)
  | _, _ -> false

and equivalent_args (fuel:nat) (xs ys:list expr)
  : Tot bool (decreases %[fuel; xs]) =
  match xs, ys with
  | [], [] -> true
  | x :: rest, y :: remaining -> equivalent fuel x y && equivalent_args fuel rest remaining
  | _, _ -> false

let lemma_quantifier_congruence (i:interpretation value) (rho:env value)
                               (k:quantifier_kind) (bs:list sort) (s:sort) (a b:expr)
  : Lemma (requires quant_extensional i /\
                    (forall (vs:list value{L.length vs = L.length bs}).
                      eval i a (shift vs rho) == eval i b (shift vs rho)))
          (ensures eval i (Quantifier k bs s a) rho == eval i (Quantifier k bs s b) rho)
  = ()

let lemma_simple_equivalent (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires B.boolean_rewrite_model i /\
                    (a = b || symmetric_equality a b || B.boolean_equiv 8 10 a b))
          (ensures eval i a rho == eval i b rho)
  = if a = b then ()
    else if symmetric_equality a b then lemma_symmetric_equality i rho a b
    else B.lemma_boolean_equiv_sound 8 10 i rho a b

let rec lemma_equivalent_args_from (fuel:nat) (i:interpretation value) (rho:env value)
                                  (xs ys:list expr)
                                  (body:(rho':env value -> a:expr -> b:expr ->
                                    Lemma (requires equivalent fuel a b)
                                          (ensures eval i a rho' == eval i b rho')))
  : Lemma (requires equivalent_args fuel xs ys)
          (ensures eval_args i xs rho == eval_args i ys rho)
          (decreases xs)
  = match xs, ys with
    | [], [] -> ()
    | x :: rest, y :: remaining ->
      body rho x y;
      lemma_equivalent_args_from fuel i rho rest remaining body
    | _, _ -> ()

let lemma_equivalent_step (fuel:nat) (i:interpretation value) (rho:env value) (a b:expr)
                          (body:(rho':env value -> x:expr -> y:expr ->
                            Lemma (requires equivalent fuel x y)
                                  (ensures eval i x rho' == eval i y rho')))
  : Lemma (requires quant_extensional i /\ N.quantifier_model i /\ B.boolean_rewrite_model i /\
                    equivalent (fuel + 1) a b)
          (ensures eval i a rho == eval i b rho)
  = if a = b || symmetric_equality a b || B.boolean_equiv 8 10 a b
    then lemma_simple_equivalent i rho a b
    else match normalize_root a, normalize_root b with
    | Some x, Some y ->
      lemma_normalize_root i rho a x;
      lemma_normalize_root i rho b y;
      if x = y || symmetric_equality x y || B.boolean_equiv 8 10 x y
      then lemma_simple_equivalent i rho x y
      else (match x, y with
            | Quantifier k bs s source, Quantifier _ _ _ target ->
              let bodies (vs:list value{L.length vs = L.length bs})
                : Lemma (eval i source (shift vs rho) == eval i target (shift vs rho))
                = body (shift vs rho) source target in
              FStar.Classical.forall_intro bodies;
              lemma_quantifier_congruence i rho k bs s source target
            | App _ args, App _ args' -> lemma_equivalent_args_from fuel i rho args args' body
            | _, _ -> ())
    | _, _ -> ()

let rec lemma_equivalent (fuel:nat) (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires quant_extensional i /\ N.quantifier_model i /\ B.boolean_rewrite_model i /\
                    equivalent fuel a b)
          (ensures eval i a rho == eval i b rho)
          (decreases fuel)
  = if fuel = 0 then ()
    else let next:nat = fuel - 1 in
      let body (rho':env value) (x y:expr)
        : Lemma (requires equivalent next x y)
                (ensures eval i x rho' == eval i y rho')
        = lemma_equivalent next i rho' x y in
      lemma_equivalent_step next i rho a b body

let lemma_equivalent_args (fuel:nat) (i:interpretation value) (rho:env value)
                          (xs ys:list expr)
  : Lemma (requires quant_extensional i /\ N.quantifier_model i /\ B.boolean_rewrite_model i /\
                    equivalent_args fuel xs ys)
          (ensures eval_args i xs rho == eval_args i ys rho)
  = let body (rho':env value) (a b:expr)
      : Lemma (requires equivalent fuel a b)
              (ensures eval i a rho' == eval i b rho')
      = lemma_equivalent fuel i rho' a b in
    lemma_equivalent_args_from fuel i rho xs ys body

let rec quantifier_bodies (args:list expr) : Tot (option (list expr)) (decreases args) =
  match args with
  | [] -> Some []
  | Quantifier _ _ _ body :: rest ->
    (match quantifier_bodies rest with
     | Some bodies -> Some (body :: bodies)
     | None -> None)
  | _ -> None

let unpush (e:expr) : option expr =
  match e with
  | App f args ->
    (match args with
     | Quantifier k bs s _ :: _ ->
       (match quantifier_bodies args with
        | Some bodies -> Some (Quantifier k bs s (App f bodies))
        | None -> None)
     | _ -> None)
  | _ -> None

let push_check (a b:expr) : bool =
  (match push a with Some result -> equivalent 64 result b | None -> false) ||
  (match unpush b with
   | Some candidate ->
     // The round trip validates all quantifier kinds, sorts, and binder lists.
     push candidate = Some b && equivalent 64 a candidate
   | None -> false)

let lemma_push_check (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires quant_extensional i /\ N.quantifier_model i /\ B.boolean_rewrite_model i /\
                    push_check a b)
          (ensures eval i a rho == eval i b rho)
  = if (match push a with Some result -> equivalent 64 result b | None -> false)
    then (match push a with
          | Some result -> lemma_push i rho a result; lemma_equivalent 64 i rho result b
          | None -> ())
    else
      match unpush b with
      | Some candidate ->
        lemma_push i rho candidate b; lemma_equivalent 64 i rho a candidate
      | None -> ()
