module Z3DatatypeLemma

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module B = Z3BooleanRewrite
module L = FStar.List.Tot

let op_constructor : decl_kind = 200
let op_recognizer : decl_kind = 201
let op_accessor : decl_kind = 202

let constructor (f:func_decl) (args:list expr) : option (int & int) =
  if f.interp <> Some op_constructor || not (sorts_match args f.domain) then None
  else match f.int_params with
  | [owner; tag; arity] ->
    if owner >= 0 && tag >= 0 && arity = L.length args then Some (owner, tag) else None
  | _ -> None

let recognizer (f:func_decl) (arg:expr) : option (int & int) =
  if f.interp <> Some op_recognizer || f.range <> bool_sort || f.domain <> [get_sort arg]
  then None
  else match f.int_params with
  | [owner; tag] -> if owner >= 0 && tag >= 0 then Some (owner, tag) else None
  | _ -> None

let accessor (f:func_decl) (arg:expr) : option (int & int & nat) =
  if f.interp <> Some op_accessor || f.domain <> [get_sort arg] then None
  else match f.int_params with
  | [owner; tag; index] ->
    if owner >= 0 && tag >= 0 && index >= 0 then Some (owner, tag, index) else None
  | _ -> None

let datatype_model (i:interpretation value) (tag:value -> (int & int))
                   (fields:value -> list value) : prop =
  (forall (f:func_decl) (args:list expr) (rho:env value) (owner c:int).
    constructor f args == Some (owner, c) ==>
    tag (eval i (App f args) rho) == (owner, c) /\
    fields (eval i (App f args) rho) == eval_args i args rho) /\
  (forall (f:func_decl) (arg:expr) (rho:env value) (owner c:int).
    recognizer f arg == Some (owner, c) ==>
    eval i (App f [arg]) rho == VBool (tag (eval i arg rho) = (owner, c))) /\
  (forall (f:func_decl) (arg:expr) (rho:env value) (owner c:int) (n:nat).
    accessor f arg == Some (owner, c, n) /\
    tag (eval i arg rho) == (owner, c) /\ n < L.length (fields (eval i arg rho)) ==>
    eval i (App f [arg]) rho == L.index (fields (eval i arg rho)) n)

let lemma_constructor (i:interpretation value) (rho:env value)
                      (tag:value -> (int & int)) (fields:value -> list value)
                      (f:func_decl) (args:list expr) (owner c:int)
  : Lemma (requires datatype_model i tag fields /\ constructor f args == Some (owner, c))
          (ensures tag (eval i (App f args) rho) == (owner, c) /\
                   fields (eval i (App f args) rho) == eval_args i args rho)
  = ()

let lemma_recognizer (i:interpretation value) (rho:env value)
                     (tag:value -> (int & int)) (fields:value -> list value)
                     (f:func_decl) (arg:expr) (owner c:int)
  : Lemma (requires datatype_model i tag fields /\ recognizer f arg == Some (owner, c))
          (ensures eval i (App f [arg]) rho == VBool (tag (eval i arg rho) = (owner, c)))
  = ()

let lemma_accessor (i:interpretation value) (rho:env value)
                   (tag:value -> (int & int)) (fields:value -> list value)
                   (f:func_decl) (arg:expr) (owner c:int) (n:nat)
  : Lemma (requires datatype_model i tag fields /\ accessor f arg == Some (owner, c, n) /\
                    tag (eval i arg rho) == (owner, c) /\ n < L.length (fields (eval i arg rho)))
          (ensures eval i (App f [arg]) rho == L.index (fields (eval i arg rho)) n)
  = ()

let rec field_equalities (xs ys:list expr) : Tot (option (list expr)) (decreases xs) =
  match xs, ys with
  | [], [] -> Some []
  | x :: rest, y :: rest' ->
    if get_sort x <> get_sort y then None
    else (match field_equalities rest rest' with
          | Some es -> Some (mk_eq_expr x y :: es)
          | None -> None)
  | _, _ -> None

let rec lemma_fields (i:interpretation value) (rho:env value) (xs ys es:list expr)
  : Lemma (requires eq_sound i /\ field_equalities xs ys == Some es)
          (ensures conj_holds i rho es <==> eval_args i xs rho == eval_args i ys rho)
          (decreases xs)
  = match xs, ys with
    | x :: rest, y :: rest' ->
      lemma_fields i rho rest rest' (Some?.v (field_equalities rest rest'))
    | _, _ -> ()

let rewrite (e:expr) : option expr =
  match e with
  | App f [App g args] ->
    let arg = App g args in
    (match constructor g args, recognizer f arg, accessor f arg with
     | Some (owner, c), Some (owner', d), _ ->
       if owner = owner' then Some (if c = d then true_expr else false_expr) else None
     | Some (owner, c), _, Some (owner', d, n) ->
       if owner = owner' && c = d && n < L.length args && f.range = get_sort (L.index args n)
       then Some (L.index args n) else None
     | _, _, _ -> None)
  | App f [App g xs; App h ys] ->
    let a, b = App g xs, App h ys in
    if f <> eq_decl (get_sort a) || get_sort a <> get_sort b then None
    else (match constructor g xs, constructor h ys with
          | Some (owner, c), Some (owner', d) ->
            if owner <> owner' then None
            else if c <> d then Some false_expr
            else if g <> h then None
            else (match field_equalities xs ys with
                  | Some es -> Some (App (B.connective_decl B.Conjunction es) es)
                  | None -> None)
          | _, _ -> None)
  | _ -> None

let lemma_rewrite (i:interpretation value) (rho:env value)
                  (tag:value -> (int & int)) (fields:value -> list value) (e result:expr)
  : Lemma (requires datatype_model i tag fields /\ B.boolean_rewrite_model i /\
                    rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App f [App g args] ->
      let arg = App g args in
      (match constructor g args, recognizer f arg, accessor f arg with
       | Some (owner, c), Some (owner', d), _ ->
         lemma_constructor i rho tag fields g args owner c;
         lemma_recognizer i rho tag fields f arg owner' d
       | Some (owner, c), _, Some (owner', d, n) ->
         lemma_constructor i rho tag fields g args owner c;
         Z3QuantifierInstantiation.lemma_eval_args_length i rho args;
         lemma_accessor i rho tag fields f arg owner' d n;
         Z3QuantifierInstantiation.lemma_eval_args_index i rho args n
       | _, _, _ -> ())
    | App f [App g xs; App h ys] ->
      let a, b = App g xs, App h ys in
      (match constructor g xs, constructor h ys with
       | Some (owner, c), Some (owner', d) ->
         lemma_constructor i rho tag fields g xs owner c;
         lemma_constructor i rho tag fields h ys owner' d;
         if c = d then
           lemma_fields i rho xs ys (Some?.v (field_equalities xs ys));
         match eval i e rho, eval i result rho with
         | VBool _, VBool _ -> ()
         | _, _ -> ()
       | _, _ -> ())
    | _ -> ()
