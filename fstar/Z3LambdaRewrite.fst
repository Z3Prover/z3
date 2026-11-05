module Z3LambdaRewrite

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
module D = Z3Definitions
module S = Z3BinderSubstitution
module N = Z3QuantifierNnf
module P = Z3QuantifierPull
module R = Z3QuantifierReduce
module B = Z3BooleanRewrite
module L = FStar.List.Tot

let const_array (f:func_decl) (v:expr) : bool =
  match f.range with
  | ArraySort bs element ->
    bs <> [] && element = get_sort v &&
    f = { decl_name = "const"; domain = [element]; range = ArraySort bs element;
          interp = Some op_const_array; int_params = [] }
  | _ -> false

let select_decl (f:func_decl) (array:expr) (args:list expr) : bool =
  match get_sort array with
  | ArraySort bs element ->
    sorts_match args bs &&
    f = { decl_name = "select"; domain = get_sort array :: bs; range = element;
          interp = Some op_select; int_params = [] }
  | _ -> false

(* Constructor/application semantics, not assumptions about rewrite proofs. *)
let lambda_model (i:interpretation value) : prop =
  (forall (bs:list sort) (a b:expr) (rho:env value).
    get_sort a == get_sort b /\
    eval i (Quantifier Lambda_k bs (quant_sort Lambda_k bs (get_sort a)) a) rho ==
    eval i (Quantifier Lambda_k bs (quant_sort Lambda_k bs (get_sort b)) b) rho ==>
    (forall (vs:list value{L.length vs = L.length bs}).
      eval i a (shift vs rho) == eval i b (shift vs rho))) /\
  (forall (f:func_decl) (bs:list sort) (body:expr) (args:list expr) (rho:env value).
    let array = Quantifier Lambda_k bs (quant_sort Lambda_k bs (get_sort body)) body in
    select_decl f array args ==>
    eval i (App f (array :: args)) rho ==
    eval i body (shift (eval_args i (L.rev args) rho) rho)) /\
  (forall (f:func_decl) (v:expr) (bs:list sort) (rho:env value).
    const_array f v /\ f.range == ArraySort bs (get_sort v) ==>
    eval i (App f [v]) rho ==
    i.interp_quant Lambda_k bs (fun _ -> eval i v rho))

let lambda_view (e:expr) : option (list sort & expr) =
  match e with
  | Quantifier Lambda_k bs s body ->
    if s = quant_sort Lambda_k bs (get_sort body) then Some (bs, body) else None
  | App f [v] ->
    if const_array f v then
      (match f.range with
       | ArraySort bs _ -> Some (bs, D.lift (L.length bs) 0 v)
       | _ -> None)
    else None
  | _ -> None

let lemma_const (i:interpretation value) (rho:env value) (f:func_decl) (v:expr) (bs:list sort)
  : Lemma (requires lambda_model i /\ const_array f v /\ f.range == ArraySort bs (get_sort v))
          (ensures eval i (App f [v]) rho ==
                   i.interp_quant Lambda_k bs (fun _ -> eval i v rho))
  = ()

let lemma_lambda_view (i:interpretation value) (rho:env value) (e:expr) (bs:list sort) (body:expr)
  : Lemma (requires quant_extensional i /\ lambda_model i /\ lambda_view e == Some (bs, body))
          (ensures get_sort e == quant_sort Lambda_k bs (get_sort body) /\
                   eval i e rho ==
                   eval i (Quantifier Lambda_k bs (quant_sort Lambda_k bs (get_sort body)) body) rho)
  = match e with
    | Quantifier _ _ _ _ -> ()
    | App f [v] ->
      assert (get_sort (D.lift (L.length bs) 0 v) == get_sort v);
      let bodies (vs:list value{L.length vs = L.length bs})
        : Lemma (eval i body (shift vs rho) == eval i v rho)
        = P.lemma_lift_under i v rho vs in
      FStar.Classical.forall_intro bodies;
      lemma_const i rho f v bs;
      assert (i.interp_quant Lambda_k bs (fun vs -> eval i body (shift vs rho)) ==
              i.interp_quant Lambda_k bs (fun _ -> eval i v rho))
    | _ -> ()

let extensional (e:expr) : option expr =
  match e with
  | App f [a; b] ->
    if f = eq_decl (get_sort a) && get_sort a = get_sort b then
      (match lambda_view a, lambda_view b with
       | Some (bs, left), Some (bs', right) ->
         if bs = bs' && get_sort left = get_sort right
         then Some (Quantifier Forall_k bs bool_sort (mk_eq_expr left right)) else None
       | _, _ -> None)
    else None
  | _ -> None

let lemma_extensional (i:interpretation value) (rho:env value) (e result:expr)
  : Lemma (requires quant_extensional i /\ lambda_model i /\ N.quantifier_model i /\
                    B.boolean_rewrite_model i /\ extensional e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App f [a; b] ->
      (match lambda_view a, lambda_view b with
       | Some (bs, left), Some (bs', right) ->
         lemma_lambda_view i rho a bs left;
         lemma_lambda_view i rho b bs' right;
         N.lemma_quantifier_truth i rho Forall_k bs (mk_eq_expr left right);
         let bodies (vs:list value{L.length vs = L.length bs})
           : Lemma (lit_true i (shift vs rho) (mk_eq_expr left right) <==>
                    eval i left (shift vs rho) == eval i right (shift vs rho)) = () in
         FStar.Classical.forall_intro bodies;
         match eval i e rho, eval i result rho with
         | VBool _, VBool _ -> ()
         | _, _ -> ()
       | _, _ -> ())
    | _ -> ()

let beta (e:expr) : option expr =
  match e with
  | App f (array :: args) ->
    if select_decl f array args then
      (match lambda_view array with
       | Some (bs, body) -> S.substitute (L.rev args) body
       | _ -> None)
    else None
  | _ -> None

let lemma_beta (i:interpretation value) (rho:env value) (e result:expr)
  : Lemma (requires quant_extensional i /\ lambda_model i /\ beta e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | App f (array :: args) ->
      (match lambda_view array with
       | Some (bs, body) ->
         lemma_lambda_view i rho array bs body;
         assert (select_decl f (Quantifier Lambda_k bs (quant_sort Lambda_k bs (get_sort body)) body) args);
         assert (eval i (App f (array :: args)) rho ==
                 eval i (App f (Quantifier Lambda_k bs (quant_sort Lambda_k bs (get_sort body)) body :: args)) rho);
         S.lemma_substitute i rho (L.rev args) body result
       | None -> ())
    | _ -> ()

let same_view (a b:expr) : bool =
  match lambda_view a, lambda_view b with
  | Some (bs, left), Some (bs', right) -> bs = bs' && R.equivalent 64 left right
  | _, _ -> false

let lemma_same_view (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires quant_extensional i /\ lambda_model i /\ N.quantifier_model i /\
                    B.boolean_rewrite_model i /\ same_view a b)
          (ensures eval i a rho == eval i b rho)
  = match lambda_view a, lambda_view b with
    | Some (bs, left), Some (bs', right) ->
      lemma_lambda_view i rho a bs left;
      lemma_lambda_view i rho b bs' right;
      let bodies (vs:list value{L.length vs = L.length bs})
        : Lemma (eval i left (shift vs rho) == eval i right (shift vs rho))
        = R.lemma_equivalent 64 i (shift vs rho) left right in
      FStar.Classical.forall_intro bodies
    | _, _ -> ()

let rewrite (a b:expr) : bool =
  match beta a, extensional a with
  | Some e, _ -> R.equivalent 64 e b
  | _, Some e -> R.equivalent 64 e b
  | _, _ -> same_view a b

let lemma_rewrite (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires quant_extensional i /\ lambda_model i /\ N.quantifier_model i /\
                    B.boolean_rewrite_model i /\ rewrite a b)
          (ensures eval i a rho == eval i b rho)
  = match beta a, extensional a with
    | Some e, _ -> lemma_beta i rho a e; R.lemma_equivalent 64 i rho e b
    | _, Some e -> lemma_extensional i rho a e; R.lemma_equivalent 64 i rho e b
    | _, _ -> lemma_same_view i rho a b
