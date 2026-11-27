module Z3Substitution

open Z3AstTheory
open FStar.List.Tot
module B = Z3ExprBinding
module L = FStar.List.Tot

type substitution = nat -> sort -> option expr

let under (count:nat) (theta:substitution) : substitution =
  fun n s ->
    if n < count then Some (Var n s)
    else match theta (n - count) s with
         | Some e -> Some (B.lift count 0 e)
         | None -> None

let rec apply (theta:substitution) (e:expr) : Tot (option expr) (decreases e) =
  match e with
  | Var n s ->
    (match theta n s with Some e' -> if get_sort e' = s then Some e' else None | None -> None)
  | App f args ->
    (match apply_args theta args with Some args' -> Some (App f args') | None -> None)
  | Quantifier k bs s body ->
    (match apply (under (L.length bs) theta) body with
     | Some body' -> Some (Quantifier k bs s body') | None -> None)

and apply_args (theta:substitution) (args:list expr)
  : Tot (option (list expr)) (decreases args) =
  match args with
  | [] -> Some []
  | e :: rest ->
    (match apply theta e, apply_args theta rest with
     | Some e', Some rest' -> Some (e' :: rest') | _, _ -> None)

let environments (#value:Type) (i:interpretation value) (theta:substitution)
                 (rho sigma:env value) : prop =
  forall (n:nat) (s:sort) (e:expr). theta n s == Some e ==> rho n == eval i e sigma

let lemma_under (#value:Type) (i:interpretation value) (theta:substitution)
                (rho sigma:env value) (vs:list value)
  : Lemma (requires quant_extensional i /\ environments i theta rho sigma)
          (ensures environments i (under (L.length vs) theta) (shift vs rho) (shift vs sigma))
  = let indices (n:nat) (s:sort) (e:expr)
      : Lemma (under (L.length vs) theta n s == Some e ==>
               shift vs rho n == eval i e (shift vs sigma))
      = if n < L.length vs then ()
        else match theta (n - L.length vs) s with
        | Some t -> B.lemma_lift_under i t sigma vs
        | None -> () in
    FStar.Classical.forall_intro_3 indices

let rec lemma_apply (#value:Type) (i:interpretation value) (theta:substitution)
                    (rho sigma:env value) (e result:expr)
  : Lemma (requires quant_extensional i /\ environments i theta rho sigma /\
                    apply theta e == Some result)
          (ensures eval i e rho == eval i result sigma /\ get_sort e == get_sort result)
          (decreases %[e])
  = match e with
    | Var _ _ -> ()
    | App _ args ->
      lemma_apply_args i theta rho sigma args (Some?.v (apply_args theta args))
    | Quantifier _ bs _ body ->
      (match apply (under (L.length bs) theta) body with
       | Some body' ->
         let bodies (vs:list value{L.length vs = L.length bs})
           : Lemma (eval i body (shift vs rho) == eval i body' (shift vs sigma))
           = lemma_under i theta rho sigma vs;
             lemma_apply i (under (L.length bs) theta) (shift vs rho) (shift vs sigma) body body' in
         FStar.Classical.forall_intro bodies
       | None -> ())

and lemma_apply_args (#value:Type) (i:interpretation value) (theta:substitution)
                     (rho sigma:env value) (args results:list expr)
  : Lemma (requires quant_extensional i /\ environments i theta rho sigma /\
                    apply_args theta args == Some results)
          (ensures eval_args i args rho == eval_args i results sigma)
          (decreases %[args])
  = match args, results with
    | [], [] -> ()
    | e :: rest, r :: remaining ->
      lemma_apply i theta rho sigma e r;
      lemma_apply_args i theta rho sigma rest remaining
    | _, _ -> ()

let arguments (args:list expr) : substitution =
  fun n s ->
    if n < L.length args
    then let e = L.index args n in if get_sort e = s then Some e else None
    else Some (Var (n - L.length args) s)

let substitute (args:list expr) (body:expr) : option expr = apply (arguments args) body

(* Definition instantiation uses an explicit variable map; declaration
   typing remains the caller's obligation, as in the legacy API. *)
let rec argument (n:nat) (variables:list nat) (args:list expr)
  : Tot (option expr) (decreases variables) =
  match variables, args with
  | v :: vs, a :: rest -> if n = v then Some a else argument n vs rest
  | _, _ -> None

let rec instantiate (depth:nat) (variables:list nat) (args:list expr) (e:expr)
  : Tot (option expr) (decreases e) =
  match e with
  | Var n s ->
    if n < depth then Some e
    else (match argument (n - depth) variables args with
         | Some a -> Some (B.lift depth 0 a)
         | None -> None)
  | App f es ->
    (match instantiate_args depth variables args es with
     | Some es' -> Some (App f es') | None -> None)
  | Quantifier k bs s b ->
    (match instantiate (depth + L.length bs) variables args b with
     | Some b' -> Some (Quantifier k bs s b') | None -> None)

and instantiate_args (depth:nat) (variables:list nat) (args es:list expr)
  : Tot (option (list expr)) (decreases es) =
  match es with
  | [] -> Some []
  | e :: rest ->
    (match instantiate depth variables args e, instantiate_args depth variables args rest with
     | Some e', Some rest' -> Some (e' :: rest') | _, _ -> None)

let rec lemma_eval_length (#value:Type) (i:interpretation value)
                         (args:list expr) (rho:env value)
  : Lemma (L.length (eval_args i args rho) == L.length args) (decreases args)
  = match args with [] -> () | _ :: rest -> lemma_eval_length i rest rho

let rec lemma_eval_index (#value:Type) (i:interpretation value) (args:list expr) (rho:env value)
                        (n:nat{n < L.length args})
  : Lemma (requires n < L.length (eval_args i args rho))
          (ensures L.index (eval_args i args rho) n == eval i (L.index args n) rho)
          (decreases args)
  = match args with
    | [] -> ()
    | _ :: rest -> if n = 0 then () else lemma_eval_index i rest rho (n - 1)

let lemma_substitute (#value:Type) (i:interpretation value) (rho:env value)
                     (args:list expr) (body result:expr)
  : Lemma (requires quant_extensional i /\ substitute args body == Some result)
          (ensures eval i body (shift (eval_args i args rho) rho) == eval i result rho)
  = lemma_eval_length i args rho;
    let indices (n:nat) (s:sort) (e:expr)
      : Lemma (arguments args n s == Some e ==>
               shift (eval_args i args rho) rho n == eval i e rho)
      = if n < L.length args then lemma_eval_index i args rho n else () in
    FStar.Classical.forall_intro_3 indices;
    lemma_apply i (arguments args) (shift (eval_args i args rho) rho) rho body result
