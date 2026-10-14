module Z3BoundedBoolEquiv

open FStar.List.Tot
module Ast = Z3AstTheory
module Basic = Z3BasicExprTheory

type nary_op =
  | And
  | Or
  | Xor

type formula (a:Type) =
  | Atom : atom:a -> formula a
  | Bool : value:bool -> formula a
  | Nary : op:nary_op -> args:list (formula a) -> formula a
  | Not : arg:formula a -> formula a
  | Implies : lhs:formula a -> rhs:formula a -> formula a
  | Eq : lhs:formula a -> rhs:formula a -> formula a

type expr = Ast.expr
type skeleton = formula expr

let neutral (op:nary_op) : bool =
  match op with And -> true | Or -> false | Xor -> false

let combine (op:nary_op) (x y:bool) : bool =
  match op with And -> x && y | Or -> x || y | Xor -> x <> y

let rec eval (#a:Type) (rho:a -> bool) (e:formula a)
  : Tot bool (decreases e)
= match e with
  | Atom a -> rho a
  | Bool b -> b
  | Nary op args -> eval_args rho op args
  | Not x -> not (eval rho x)
  | Implies x y -> not (eval rho x) || eval rho y
  | Eq x y -> eval rho x = eval rho y

and eval_args (#a:Type) (rho:a -> bool) (op:nary_op)
    (args:list (formula a)) : Tot bool (decreases args)
= match args with
  | [] -> neutral op
  | x :: xs -> combine op (eval rho x) (eval_args rho op xs)

type bool_op =
  | BTrue
  | BFalse
  | BNary : op:nary_op -> bool_op
  | BNot
  | BImplies
  | BEq
  | Opaque

let is_bool (e:expr) : bool = Ast.sort_eq (Ast.get_sort e) Ast.bool_sort

let rec bool_domain (domain:list Ast.sort)
  : Tot bool (decreases domain)
= match domain with
  | [] -> true
  | s :: tl -> Ast.sort_eq s Ast.bool_sort && bool_domain tl

let rec bool_args (args:list expr) : Tot bool (decreases args)
= match args with
  | [] -> true
  | a :: tl -> is_bool a && bool_args tl

(* Use the existing basic-family tags, never declaration names. Equality
   over non-Boolean arguments and malformed applications stay opaque. *)
let classify (f:Ast.func_decl) (arity:nat) : bool_op =
  if not (Ast.sort_eq f.range Ast.bool_sort &&
          bool_domain f.domain && length f.domain = arity &&
          f.int_params = []) then Opaque
  else if Basic.is_basic_op f Basic.Op_true && arity = 0 then BTrue
  else if Basic.is_basic_op f Basic.Op_false && arity = 0 then BFalse
  else if Basic.is_basic_op f Basic.Op_and then BNary And
  else if Basic.is_basic_op f Basic.Op_or then BNary Or
  else if Basic.is_basic_op f Basic.Op_xor then BNary Xor
  else if Basic.is_basic_op f Basic.Op_not && arity = 1 then BNot
  else if Basic.is_basic_op f Basic.Op_implies && arity = 2 then BImplies
  else if Basic.is_basic_op f Basic.Op_eq && arity = 2 then BEq
  else Opaque

let classify_app (f:Ast.func_decl) (args:list expr) : bool_op =
  if Ast.sorts_match args f.domain then classify f (length args) else Opaque

(* Check shared boundaries before inspecting children, regardless of the
   remaining depth at this occurrence. *)
let rec cut_with_boundaries (boundaries:list expr) (depth:nat) (e:expr)
  : Tot skeleton (decreases e)
= if mem e boundaries then Atom e
  else match e with
  | Ast.Var _ _ -> Atom e
  | Ast.Quantifier _ _ _ _ -> Atom e
  | Ast.App f args ->
    match classify_app f args with
    | BTrue -> Bool true
    | BFalse -> Bool false
    | BNary op ->
      if depth = 0 then Atom e
      else Nary op (cut_args_with_boundaries boundaries (depth - 1) args)
    | BNot ->
      (match args with
       | [x] ->
         if depth = 0 then Atom e
         else Not (cut_with_boundaries boundaries (depth - 1) x)
       | _ -> Atom e)
    | BImplies ->
      (match args with
       | [x; y] ->
         if depth = 0 then Atom e
         else Implies (cut_with_boundaries boundaries (depth - 1) x)
                      (cut_with_boundaries boundaries (depth - 1) y)
       | _ -> Atom e)
    | BEq ->
      (match args with
       | [x; y] ->
         if depth = 0 then Atom e
         else Eq (cut_with_boundaries boundaries (depth - 1) x)
                 (cut_with_boundaries boundaries (depth - 1) y)
       | _ -> Atom e)
    | Opaque -> Atom e

and cut_args_with_boundaries (boundaries:list expr) (depth:nat) (args:list expr)
  : Tot (list skeleton) (decreases args)
= match args with
  | [] -> []
  | x :: xs ->
    cut_with_boundaries boundaries depth x ::
    cut_args_with_boundaries boundaries depth xs

let cut (depth:nat) (e:expr) : skeleton =
  cut_with_boundaries [] depth e

let cut_args (depth:nat) (args:list expr) : list skeleton =
  cut_args_with_boundaries [] depth args

(* Include nodes at the cutoff, but never descend through opaque nodes.
   Constants need no atom and are excluded from boundary discovery. *)
let rec candidate_nodes (depth:nat) (e:expr)
  : Tot (list expr) (decreases e)
= match e with
  | Ast.Var _ _ -> [e]
  | Ast.Quantifier _ _ _ _ -> [e]
  | Ast.App f args ->
    match classify_app f args with
    | BTrue -> []
    | BFalse -> []
    | Opaque -> [e]
    | _ ->
      e :: (if depth = 0 then [] else candidate_args (depth - 1) args)

and candidate_args (depth:nat) (args:list expr)
  : Tot (list expr) (decreases args)
= match args with
  | [] -> []
  | x :: xs -> append (candidate_nodes depth x) (candidate_args depth xs)

let rec support (#a:Type) (e:formula a)
  : Tot (list a) (decreases e)
= match e with
  | Atom a -> [a]
  | Bool _ -> []
  | Nary _ args -> support_args args
  | Not x -> support x
  | Implies x y -> append (support x) (support y)
  | Eq x y -> append (support x) (support y)

and support_args (#a:Type) (args:list (formula a))
  : Tot (list a) (decreases args)
= match args with
  | [] -> []
  | x :: xs -> append (support x) (support_args xs)

let rec unique (#a:eqtype) (xs:list a)
  : Tot (list a) (decreases xs)
= match xs with
  | [] -> []
  | x :: tl ->
    let rest = unique tl in
    if mem x rest then rest else x :: rest

let rec intersect (#a:eqtype) (xs ys:list a)
  : Tot (list a) (decreases xs)
= match xs with
  | [] -> []
  | x :: tl ->
    if mem x ys then x :: intersect tl ys else intersect tl ys

let common_boundaries (depth:nat) (s t:expr) : list expr =
  unique (intersect (candidate_nodes depth s) (candidate_nodes depth t))

let update (#a:eqtype) (rho:a -> bool) (x:a) (b:bool) : a -> bool =
  fun y -> if y = x then b else rho y

(* Stream the truth-table rows in a common variable order. No independent
   renaming or permutation of the two formulas' atoms is allowed. *)
let rec check_rows (atoms:list expr) (rho:expr -> bool) (s t:skeleton)
  : Tot bool (decreases atoms)
= match atoms with
  | [] -> eval rho s = eval rho t
  | a :: tl ->
    check_rows tl (update rho a false) s t &&
    check_rows tl (update rho a true) s t

let bounded_bool_equiv (depth:nat) (width:nat) (s t:expr) : bool =
  if s = t then true
  else if not (is_bool s && is_bool t) then false
  else
    let boundaries = common_boundaries depth s t in
    let cs = cut_with_boundaries boundaries depth s in
    let ct = cut_with_boundaries boundaries depth t in
    let atoms = unique (append (support cs) (support ct)) in
    if length atoms > width then false
    else check_rows atoms (fun _ -> false) cs ct

let lemma_bounded_width (depth:nat) (width:nat) (s t:expr)
  : Lemma
      (requires bounded_bool_equiv depth width s t /\ s <> t)
      (ensures
        (let boundaries = common_boundaries depth s t in
        length (unique
          (append (support (cut_with_boundaries boundaries depth s))
                  (support (cut_with_boundaries boundaries depth t)))) <= width))
= ()

let rec lemma_mem_append (#a:eqtype) (xs ys:list a)
  : Lemma
      (forall x. mem x (append xs ys) <==> mem x xs \/ mem x ys)
      (decreases xs)
= match xs with
  | [] -> ()
  | _ :: tl -> lemma_mem_append tl ys

let rec lemma_unique_mem (#a:eqtype) (xs:list a)
  : Lemma (forall x. mem x (unique xs) <==> mem x xs)
      (decreases xs)
= match xs with
  | [] -> ()
  | _ :: tl -> lemma_unique_mem tl

let rec lemma_intersect_mem (#a:eqtype) (xs ys:list a)
  : Lemma
      (forall x. mem x (intersect xs ys) <==> mem x xs /\ mem x ys)
      (decreases xs)
= match xs with
  | [] -> ()
  | _ :: tl -> lemma_intersect_mem tl ys

let lemma_common_boundaries (depth:nat) (s t:expr)
  : Lemma
      (forall x. mem x (common_boundaries depth s t) <==>
        mem x (candidate_nodes depth s) /\ mem x (candidate_nodes depth t))
= lemma_intersect_mem (candidate_nodes depth s) (candidate_nodes depth t);
  lemma_unique_mem (intersect (candidate_nodes depth s) (candidate_nodes depth t))

let lemma_cut_at_boundary (boundaries:list expr) (depth:nat) (e:expr)
  : Lemma
      (requires mem e boundaries)
      (ensures cut_with_boundaries boundaries depth e == Atom e)
= ()

let rec lemma_eval_agree (#a:eqtype) (rho sigma:a -> bool) (e:formula a)
  : Lemma
      (requires forall x. mem x (support e) ==> rho x == sigma x)
      (ensures eval rho e == eval sigma e)
      (decreases e)
= match e with
  | Atom _ -> ()
  | Bool _ -> ()
  | Nary op args -> lemma_eval_args_agree rho sigma op args
  | Not x -> lemma_eval_agree rho sigma x
  | Implies x y ->
    lemma_mem_append (support x) (support y);
    lemma_eval_agree rho sigma x;
    lemma_eval_agree rho sigma y
  | Eq x y ->
    lemma_mem_append (support x) (support y);
    lemma_eval_agree rho sigma x;
    lemma_eval_agree rho sigma y

and lemma_eval_args_agree (#a:eqtype) (rho sigma:a -> bool)
    (op:nary_op) (args:list (formula a))
  : Lemma
      (requires forall x. mem x (support_args args) ==> rho x == sigma x)
      (ensures eval_args rho op args == eval_args sigma op args)
      (decreases args)
= match args with
  | [] -> ()
  | x :: xs ->
    lemma_mem_append (support x) (support_args xs);
    lemma_eval_agree rho sigma x;
    lemma_eval_args_agree rho sigma op xs

let agree_outside (atoms:list expr) (rho sigma:expr -> bool)
    (s t:skeleton) : prop =
  forall x.
    (mem x (support s) \/ mem x (support t)) /\ not (mem x atoms)
    ==> rho x == sigma x

let rec lemma_check_rows_sound (atoms:list expr) (rho sigma:expr -> bool)
    (s t:skeleton)
  : Lemma
      (requires check_rows atoms rho s t /\ agree_outside atoms rho sigma s t)
      (ensures eval sigma s == eval sigma t)
      (decreases atoms)
= match atoms with
  | [] ->
    lemma_eval_agree rho sigma s;
    lemma_eval_agree rho sigma t
  | a :: tl ->
    let next = update rho a (sigma a) in
    assert (agree_outside tl next sigma s t);
    if sigma a then lemma_check_rows_sound tl next sigma s t
    else lemma_check_rows_sound tl next sigma s t

(* Z3AstTheory intentionally leaves all operators' meanings abstract.
   This contract supplies Boolean representation and the usual one-layer
   connective laws, not equivalence of the inputs or correctness of the checker. *)
let ast_valuation (#value:Type) (i:Ast.interpretation value)
    (decode:value -> bool) (rho:Ast.env value) : expr -> bool =
  fun a -> decode (Ast.eval i a rho)

let boolean_semantics (#value:Type) (i:Ast.interpretation value)
    (encode:bool -> value) (decode:value -> bool) (rho:Ast.env value) : prop =
  (forall b. decode (encode b) == b) /\
  (forall (e:expr).
    is_bool e ==>
    Ast.eval i e rho ==
      encode (eval (ast_valuation i decode rho) (cut 1 e)))

let rec lemma_sorted_bool_args (args:list expr) (domain:list Ast.sort)
  : Lemma
      (requires Ast.sorts_match args domain /\ bool_domain domain)
      (ensures bool_args args)
      (decreases args)
= match args, domain with
  | [], _ -> ()
  | _ :: tl, _ :: rest -> lemma_sorted_bool_args tl rest

let lemma_classified_args (f:Ast.func_decl) (args:list expr)
  : Lemma
      (requires classify_app f args <> Opaque)
      (ensures bool_args args)
= lemma_sorted_bool_args args f.domain

let rec lemma_cut_with_boundaries_sound (#value:Type)
    (boundaries:list expr) (depth:nat)
    (i:Ast.interpretation value) (encode:bool -> value)
    (decode:value -> bool) (rho:Ast.env value) (e:expr)
  : Lemma
      (requires boolean_semantics i encode decode rho /\ is_bool e)
      (ensures
        eval (ast_valuation i decode rho)
          (cut_with_boundaries boundaries depth e) ==
        decode (Ast.eval i e rho))
      (decreases e)
= if mem e boundaries then ()
  else
  let sigma = ast_valuation i decode rho in
  assert (Ast.eval i e rho == encode (eval sigma (cut 1 e)));
  match e with
  | Ast.Var _ _ -> ()
  | Ast.Quantifier _ _ _ _ -> ()
  | Ast.App f args ->
    match classify_app f args with
    | BTrue -> ()
    | BFalse -> ()
    | BNary op ->
      if depth = 0 then ()
      else (
        lemma_classified_args f args;
        lemma_cut_args_with_boundaries_sound boundaries (depth - 1)
          i encode decode rho op args
      )
    | BNot ->
      (match args with
       | [x] ->
         if depth = 0 then ()
         else (
           lemma_classified_args f args;
           lemma_cut_with_boundaries_sound boundaries (depth - 1)
             i encode decode rho x;
           lemma_cut_with_boundaries_sound [] 0 i encode decode rho x
         )
       | _ -> ())
    | BImplies ->
      (match args with
       | [x; y] ->
         if depth = 0 then ()
         else (
           lemma_classified_args f args;
           lemma_cut_with_boundaries_sound boundaries (depth - 1)
             i encode decode rho x;
           lemma_cut_with_boundaries_sound [] 0 i encode decode rho x;
           lemma_cut_with_boundaries_sound boundaries (depth - 1)
             i encode decode rho y;
           lemma_cut_with_boundaries_sound [] 0 i encode decode rho y
         )
       | _ -> ())
    | BEq ->
      (match args with
       | [x; y] ->
         if depth = 0 then ()
         else (
           lemma_classified_args f args;
           lemma_cut_with_boundaries_sound boundaries (depth - 1)
             i encode decode rho x;
           lemma_cut_with_boundaries_sound [] 0 i encode decode rho x;
           lemma_cut_with_boundaries_sound boundaries (depth - 1)
             i encode decode rho y;
           lemma_cut_with_boundaries_sound [] 0 i encode decode rho y
         )
       | _ -> ())
    | Opaque -> ()

and lemma_cut_args_with_boundaries_sound (#value:Type)
    (boundaries:list expr) (depth:nat)
    (i:Ast.interpretation value) (encode:bool -> value)
    (decode:value -> bool) (rho:Ast.env value) (op:nary_op) (args:list expr)
  : Lemma
      (requires boolean_semantics i encode decode rho /\ bool_args args)
      (ensures
        eval_args (ast_valuation i decode rho) op
          (cut_args_with_boundaries boundaries depth args) ==
        eval_args (ast_valuation i decode rho) op (cut_args 0 args))
      (decreases args)
= match args with
  | [] -> ()
  | x :: xs ->
    lemma_cut_with_boundaries_sound boundaries depth i encode decode rho x;
    lemma_cut_with_boundaries_sound [] 0 i encode decode rho x;
    lemma_cut_args_with_boundaries_sound boundaries depth i encode decode rho op xs

let lemma_cut_sound (#value:Type) (depth:nat)
    (i:Ast.interpretation value) (encode:bool -> value)
    (decode:value -> bool) (rho:Ast.env value) (e:expr)
  : Lemma
      (requires boolean_semantics i encode decode rho /\ is_bool e)
      (ensures
        eval (ast_valuation i decode rho) (cut depth e) ==
        decode (Ast.eval i e rho))
= lemma_cut_with_boundaries_sound [] depth i encode decode rho e

(* The interpretation and variable environment are arbitrary, subject only
   to Boolean semantics. False still means "not established". *)
let lemma_bounded_bool_equiv_sound (#value:Type) (depth:nat) (width:nat)
    (s t:expr) (i:Ast.interpretation value)
    (encode:bool -> value) (decode:value -> bool) (rho:Ast.env value)
  : Lemma
      (requires boolean_semantics i encode decode rho /\
                bounded_bool_equiv depth width s t)
      (ensures Ast.eval i s rho == Ast.eval i t rho)
= if s = t then ()
  else (
    let boundaries = common_boundaries depth s t in
    let cs = cut_with_boundaries boundaries depth s in
    let ct = cut_with_boundaries boundaries depth t in
    let atoms = unique (append (support cs) (support ct)) in
    let sigma = ast_valuation i decode rho in
    lemma_mem_append (support cs) (support ct);
    lemma_unique_mem (append (support cs) (support ct));
    assert (agree_outside atoms (fun _ -> false) sigma cs ct);
    lemma_check_rows_sound atoms (fun _ -> false) sigma cs ct;
    lemma_cut_with_boundaries_sound boundaries depth i encode decode rho s;
    lemma_cut_with_boundaries_sound boundaries depth i encode decode rho t;
    assert (Ast.eval i s rho == encode (eval sigma (cut 1 s)));
    assert (Ast.eval i t rho == encode (eval sigma (cut 1 t)));
    lemma_cut_sound 1 i encode decode rho s;
    lemma_cut_sound 1 i encode decode rho t
  )

let rec fold_values (op:nary_op) (vs:list bool)
  : Tot bool (decreases vs)
= match vs with
  | [] -> neutral op
  | v :: tl -> combine op v (fold_values op tl)

(* A concrete family of native interpretations witnesses the semantic
   contract. All non-Boolean operators and quantifiers keep their fallback. *)
let boolean_interp_app (fallback:Ast.interpretation bool)
    (f:Ast.func_decl{Some? f.interp}) (vs:list bool) : bool =
  match classify f (length vs) with
  | BTrue -> true
  | BFalse -> false
  | BNary op -> fold_values op vs
  | BNot ->
    (match vs with [x] -> not x | _ -> fallback.interp_app f vs)
  | BImplies ->
    (match vs with [x; y] -> not x || y | _ -> fallback.interp_app f vs)
  | BEq ->
    (match vs with [x; y] -> x = y | _ -> fallback.interp_app f vs)
  | Opaque -> fallback.interp_app f vs

let boolean_interpretation (fallback:Ast.interpretation bool)
  : Ast.interpretation bool =
  { interp_app = boolean_interp_app fallback;
    uninterp_app = fallback.uninterp_app;
    interp_quant = fallback.interp_quant }

let id_bool (b:bool) : bool = b

let rec lemma_ast_args_length (#value:Type) (i:Ast.interpretation value)
    (rho:Ast.env value) (args:list expr)
  : Lemma (length (Ast.eval_args i args rho) == length args)
      (decreases args)
= match args with
  | [] -> ()
  | _ :: tl -> lemma_ast_args_length i rho tl

let lemma_native_cut_zero (fallback:Ast.interpretation bool)
    (rho:Ast.env bool) (e:expr)
  : Lemma
      (eval (ast_valuation (boolean_interpretation fallback) id_bool rho)
        (cut 0 e) == Ast.eval (boolean_interpretation fallback) e rho)
= match e with
  | Ast.Var _ _ -> ()
  | Ast.Quantifier _ _ _ _ -> ()
  | Ast.App f args ->
    lemma_ast_args_length (boolean_interpretation fallback) rho args;
    match classify_app f args with
    | BTrue -> ()
    | BFalse -> ()
    | _ -> ()

let rec lemma_native_cut_args (fallback:Ast.interpretation bool)
    (rho:Ast.env bool) (op:nary_op) (args:list expr)
  : Lemma
      (eval_args
        (ast_valuation (boolean_interpretation fallback) id_bool rho)
        op (cut_args 0 args) ==
       fold_values op (Ast.eval_args (boolean_interpretation fallback) args rho))
      (decreases args)
= match args with
  | [] -> ()
  | x :: xs ->
    lemma_native_cut_zero fallback rho x;
    lemma_native_cut_args fallback rho op xs

let lemma_native_boolean_step (fallback:Ast.interpretation bool)
    (rho:Ast.env bool) (e:expr)
  : Lemma
      (Ast.eval (boolean_interpretation fallback) e rho ==
       eval (ast_valuation (boolean_interpretation fallback) id_bool rho)
         (cut 1 e))
= match e with
  | Ast.Var _ _ -> ()
  | Ast.Quantifier _ _ _ _ -> ()
  | Ast.App f args ->
    lemma_ast_args_length (boolean_interpretation fallback) rho args;
    match classify_app f args with
    | BTrue -> ()
    | BFalse -> ()
    | BNary op -> lemma_native_cut_args fallback rho op args
    | BNot ->
      (match args with [x] -> lemma_native_cut_zero fallback rho x | _ -> ())
    | BImplies ->
      (match args with
       | [x; y] ->
         lemma_native_cut_zero fallback rho x;
         lemma_native_cut_zero fallback rho y
       | _ -> ())
    | BEq ->
      (match args with
       | [x; y] ->
         lemma_native_cut_zero fallback rho x;
         lemma_native_cut_zero fallback rho y
       | _ -> ())
    | Opaque -> ()

let lemma_boolean_interpretation_semantics (fallback:Ast.interpretation bool)
    (rho:Ast.env bool)
  : Lemma
      (boolean_semantics (boolean_interpretation fallback) id_bool id_bool rho)
= FStar.Classical.forall_intro (lemma_native_boolean_step fallback rho)

let lemma_bounded_bool_equiv_boolean_sound (depth:nat) (width:nat)
    (s t:expr) (fallback:Ast.interpretation bool) (rho:Ast.env bool)
  : Lemma
      (requires bounded_bool_equiv depth width s t)
      (ensures
        Ast.eval (boolean_interpretation fallback) s rho ==
        Ast.eval (boolean_interpretation fallback) t rho)
= lemma_boolean_interpretation_semantics fallback rho;
  lemma_bounded_bool_equiv_sound depth width s t
    (boolean_interpretation fallback) id_bool id_bool rho
