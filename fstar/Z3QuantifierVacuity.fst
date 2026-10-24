module Z3QuantifierVacuity

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
module Q = Z3QuantifierNnf
module L = FStar.List.Tot

let rec erase (#a:Type) (n:nat) (xs:list a) : Tot (list a) (decreases xs) =
  match xs with
  | [] -> []
  | x :: rest -> if n = 0 then rest else x :: erase (n - 1) rest

let rec insert (#a:Type) (n:nat) (x:a) (xs:list a)
  : Tot (list a) (decreases xs) =
  if n = 0 then x :: xs
  else match xs with
  | [] -> [x]
  | y :: rest -> y :: insert (n - 1) x rest

let rec lemma_erase_length (#a:Type) (n:nat) (xs:list a)
  : Lemma (requires n < L.length xs)
          (ensures L.length (erase n xs) + 1 == L.length xs)
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> if n > 0 then lemma_erase_length (n - 1) rest

let rec lemma_erase_index (#a:Type) (n j:nat) (xs:list a)
  : Lemma (requires n < L.length xs /\ j < L.length xs /\ j <> n)
          (ensures
            (if j < n then j else j - 1) < L.length (erase n xs) /\
            L.index (erase n xs) (if j < n then j else j - 1) == L.index xs j)
          (decreases xs) =
  match xs with
  | [] -> ()
  | _ :: rest ->
    lemma_erase_length n xs;
    if n > 0 && j > 0 then lemma_erase_index (n - 1) (j - 1) rest

let rec lemma_insert_erase (#a:Type) (n:nat) (x:a) (xs:list a)
  : Lemma (requires n <= L.length xs)
          (ensures erase n (insert n x xs) == xs /\
                   L.length (insert n x xs) == L.length xs + 1)
          (decreases xs) =
  if n > 0 then
    match xs with [] -> () | _ :: rest -> lemma_insert_erase (n - 1) x rest

let removed_environment (cutoff:nat) (source target:env value) : prop =
  forall (n:nat). n <> cutoff ==> source n == target (if n < cutoff then n else n - 1)

let lemma_removed_shift (cutoff:nat) (source target:env value) (vs:list value)
  : Lemma (requires removed_environment cutoff source target)
          (ensures removed_environment (cutoff + L.length vs) (shift vs source) (shift vs target)) =
  let aux (n:nat{n <> cutoff + L.length vs}) : Lemma
      (shift vs source n ==
       shift vs target (if n < cutoff + L.length vs then n else n - 1)) = ()
  in FStar.Classical.forall_intro aux

let lemma_erased_environment (n:nat) (vs:list value) (rho:env value)
  : Lemma (requires n < L.length vs)
          (ensures removed_environment n (shift vs rho) (shift (erase n vs) rho)) =
  lemma_erase_length n vs;
  let aux (j:nat{j <> n}) : Lemma
      (shift vs rho j ==
       shift (erase n vs) rho (if j < n then j else j - 1)) =
    if j < L.length vs then lemma_erase_index n j vs
  in FStar.Classical.forall_intro aux

(* Failing at the removed variable is essential: lowering is a partial
   renaming, not substitution of an arbitrary value for a used binder. *)
let rec lower (cutoff:nat) (e:expr) : Tot (option expr) (decreases e) =
  match e with
  | Var n s ->
    if n = cutoff then None else Some (Var (if n < cutoff then n else n - 1) s)
  | App f args ->
    (match lower_args cutoff args with Some xs -> Some (App f xs) | None -> None)
  | Quantifier k bs s body ->
    (match lower (cutoff + L.length bs) body with
     | Some b -> Some (Quantifier k bs s b) | None -> None)

and lower_args (cutoff:nat) (args:list expr)
  : Tot (option (list expr)) (decreases args) =
  match args with
  | [] -> Some []
  | a :: rest ->
    (match lower cutoff a, lower_args cutoff rest with
     | Some b, Some xs -> Some (b :: xs) | _, _ -> None)

let rec lemma_lower_sound (cutoff:nat) (e result:expr)
                          (i:interpretation value) (source target:env value)
  : Lemma (requires quant_extensional i /\ lower cutoff e == Some result /\
                    removed_environment cutoff source target)
          (ensures eval i e source == eval i result target)
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App _ args ->
    lemma_lower_args_sound cutoff args (Some?.v (lower_args cutoff args)) i source target
  | Quantifier k bs s body ->
    let b = Some?.v (lower (cutoff + L.length bs) body) in
    let aux (vs:list value{L.length vs = L.length bs})
      : Lemma (eval i body (shift vs source) == eval i b (shift vs target)) =
      lemma_removed_shift cutoff source target vs;
      lemma_lower_sound (cutoff + L.length bs) body b i (shift vs source) (shift vs target)
    in FStar.Classical.forall_intro aux

and lemma_lower_args_sound (cutoff:nat) (args results:list expr)
                           (i:interpretation value) (source target:env value)
  : Lemma (requires quant_extensional i /\ lower_args cutoff args == Some results /\
                    removed_environment cutoff source target)
          (ensures eval_args i args source == eval_args i results target)
          (decreases args) =
  match args, results with
  | a :: rest, b :: xs ->
    lemma_lower_sound cutoff a b i source target;
    lemma_lower_args_sound cutoff rest xs i source target
  | _, _ -> ()

let lemma_lower_sort (cutoff:nat) (e result:expr)
  : Lemma (requires lower cutoff e == Some result)
          (ensures get_sort e == get_sort result) =
  match e with Var _ _ | App _ _ | Quantifier _ _ _ _ -> ()

let all_assignments (i:interpretation value) (rho:env value)
                    (count:nat) (body:expr) (truth:bool) : prop =
  forall (vs:list value{L.length vs = count}).
    (lit_true i (shift vs rho) body <==> truth)

let lemma_all_assignments (n count:nat) (body result:expr) (truth:bool)
                          (i:interpretation value) (rho:env value)
  : Lemma (requires quant_extensional i /\ n < count /\ lower n body == Some result)
          (ensures all_assignments i rho count body truth <==>
                   all_assignments i rho (count - 1) result truth) =
  FStar.Classical.impl_intro
    #(all_assignments i rho count body truth)
    #(all_assignments i rho (count - 1) result truth)
    (fun _ ->
      let aux (vs:list value{L.length vs = count - 1})
        : Lemma (lit_true i (shift vs rho) result <==> truth) =
        lemma_insert_erase n (VBool false) vs;
        let full = insert n (VBool false) vs in
        lemma_erased_environment n full rho;
        lemma_lower_sound n body result i (shift full rho) (shift vs rho)
      in FStar.Classical.forall_intro aux);
  FStar.Classical.impl_intro
    #(all_assignments i rho (count - 1) result truth)
    #(all_assignments i rho count body truth)
    (fun _ ->
      let aux (vs:list value{L.length vs = count})
        : Lemma (lit_true i (shift vs rho) body <==> truth) =
        lemma_erase_length n vs;
        lemma_erased_environment n vs rho;
        lemma_lower_sound n body result i (shift vs rho) (shift (erase n vs) rho)
      in FStar.Classical.forall_intro aux)

let quantified (k:quantifier_kind) (bs:list sort) (body:expr) : expr =
  if bs = [] then body else Quantifier k bs bool_sort body

let rec lemma_same_environment (e:expr) (i:interpretation value) (source target:env value)
  : Lemma (requires quant_extensional i /\ (forall (n:nat). source n == target n))
          (ensures eval i e source == eval i e target)
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App _ args -> lemma_same_environment_args args i source target
  | Quantifier _ bs _ body ->
    let aux (vs:list value{L.length vs = L.length bs})
      : Lemma (eval i body (shift vs source) == eval i body (shift vs target)) =
      let pointwise (n:nat) : Lemma (shift vs source n == shift vs target n) = () in
      FStar.Classical.forall_intro pointwise;
      lemma_same_environment body i (shift vs source) (shift vs target)
    in FStar.Classical.forall_intro aux

and lemma_same_environment_args (args:list expr) (i:interpretation value)
                                (source target:env value)
  : Lemma (requires quant_extensional i /\ (forall (n:nat). source n == target n))
          (ensures eval_args i args source == eval_args i args target)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_same_environment a i source target;
    lemma_same_environment_args rest i source target

let lemma_quantified_truth (i:interpretation value) (rho:env value)
                           (k:quantifier_kind) (bs:list sort) (body:expr)
  : Lemma (requires Q.quantifier_model i /\ quant_extensional i /\ get_sort body == bool_sort /\
                    (k = Forall_k \/ k = Exists_k))
          (ensures lit_true i rho (quantified k bs body) <==>
            (if k = Forall_k then all_assignments i rho (L.length bs) body true
             else ~(all_assignments i rho (L.length bs) body false))) =
  if bs <> [] then Q.lemma_quantifier_truth i rho k bs body
  else (
    let aux (vs:list value{L.length vs = 0})
      : Lemma (lit_true i (shift vs rho) body <==> lit_true i rho body) =
      (match vs with [] -> () | _ :: _ -> ());
      let pointwise (n:nat) : Lemma (shift vs rho n == rho n) = () in
      FStar.Classical.forall_intro pointwise;
      lemma_same_environment body i (shift vs rho) rho
    in
    FStar.Classical.forall_intro aux;
    aux [];
    FStar.Classical.excluded_middle (lit_true i rho body))

let remove (n:nat) (e:expr) : option expr =
  match e with
  | Quantifier k bs s body ->
    if (k = Forall_k || k = Exists_k) && s = bool_sort &&
       get_sort body = bool_sort && n < L.length bs then
      (match lower n body with
       | Some b -> Some (quantified k (L.rev (erase n (L.rev bs))) b)
       | None -> None)
    else None
  | _ -> None

let lemma_remove_sound (n:nat) (e result:expr)
                       (i:interpretation value) (rho:env value)
  : Lemma (requires Q.quantifier_model i /\ boolean_model i /\ quant_extensional i /\
                    remove n e == Some result)
          (ensures eval i e rho == eval i result rho) =
  match e with
  | Quantifier k bs s body ->
    let b = Some?.v (lower n body) in
    let bs' = L.rev (erase n (L.rev bs)) in
    FStar.List.Tot.Properties.rev_length bs;
    lemma_erase_length n (L.rev bs);
    FStar.List.Tot.Properties.rev_length (erase n (L.rev bs));
    lemma_lower_sort n body b;
    Q.lemma_quantifier_truth i rho k bs body;
    lemma_quantified_truth i rho k bs' b;
    lemma_all_assignments n (L.length bs) body b true i rho;
    lemma_all_assignments n (L.length bs) body b false i rho;
    (match bs' with [] -> () | _ :: _ -> ());
    (match eval i e rho, eval i result rho with VBool _, VBool _ -> () | _, _ -> ())
  | _ -> ()

let rec first_removal (remaining:nat) (n:nat) (e:expr)
  : Tot (option expr) (decreases remaining) =
  if remaining = 0 then None
  else match remove n e with
  | Some b -> Some b
  | None -> first_removal (remaining - 1) (n + 1) e

let rec lemma_first_removal_sound (remaining n:nat) (e result:expr)
                                  (i:interpretation value) (rho:env value)
  : Lemma (requires Q.quantifier_model i /\ boolean_model i /\ quant_extensional i /\
                    first_removal remaining n e == Some result)
          (ensures eval i e rho == eval i result rho)
          (decreases remaining) =
  if remaining > 0 then
    match remove n e with
    | Some _ -> lemma_remove_sound n e result i rho
    | None -> lemma_first_removal_sound (remaining - 1) (n + 1) e result i rho

let step (e:expr) : option expr =
  match e with Quantifier _ bs _ _ -> first_removal (L.length bs) 0 e | _ -> None

let lemma_step_sound (e result:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires Q.quantifier_model i /\ boolean_model i /\ quant_extensional i /\
                    step e == Some result)
          (ensures eval i e rho == eval i result rho) =
  match e with
  | Quantifier _ bs _ _ -> lemma_first_removal_sound (L.length bs) 0 e result i rho
  | _ -> ()

let rec equivalent (fuel:nat) (s t:expr) : Tot bool (decreases %[fuel; 0]) =
  if s = t then true
  else if fuel = 0 then false
  else
    let _ = assert (fuel > 0) in
    match step s, step t with
    | Some a, _ -> equivalent (fuel - 1) a t
    | None, Some b -> equivalent (fuel - 1) s b
    | None, None ->
      (match s, t with
       | App f xs, App g ys -> f = g && equivalent_args (fuel - 1) xs ys
       | Quantifier k bs q body, Quantifier k' bs' q' body' ->
         k = k' && bs = bs' && q = q' && equivalent (fuel - 1) body body'
       | _, _ -> false)

and equivalent_args (fuel:nat) (xs ys:list expr)
  : Tot bool (decreases %[fuel; L.length xs + 1]) =
  match xs, ys with
  | [], [] -> true
  | x :: rest, y :: tail -> equivalent fuel x y && equivalent_args fuel rest tail
  | _, _ -> false

let rec lemma_equivalent_sound (fuel:nat) (s t:expr)
                               (i:interpretation value) (rho:env value)
  : Lemma (requires Q.quantifier_model i /\ boolean_model i /\ quant_extensional i /\
                    equivalent fuel s t)
          (ensures eval i s rho == eval i t rho)
          (decreases %[fuel; 0]) =
  if s = t || fuel = 0 then ()
  else (
    match step s, step t with
    | Some a, _ ->
      lemma_step_sound s a i rho;
      lemma_equivalent_sound (fuel - 1) a t i rho
    | None, Some b ->
      lemma_step_sound t b i rho;
      lemma_equivalent_sound (fuel - 1) s b i rho
    | None, None ->
      (match s, t with
       | App _ xs, App _ ys -> lemma_equivalent_args_sound (fuel - 1) xs ys i rho
       | Quantifier _ bs _ body, Quantifier _ _ _ body' ->
         let aux (vs:list value{L.length vs = L.length bs})
           : Lemma (eval i body (shift vs rho) == eval i body' (shift vs rho)) =
           lemma_equivalent_sound (fuel - 1) body body' i (shift vs rho)
         in FStar.Classical.forall_intro aux
       | _, _ -> ()))

and lemma_equivalent_args_sound (fuel:nat) (xs ys:list expr)
                                (i:interpretation value) (rho:env value)
  : Lemma (requires Q.quantifier_model i /\ boolean_model i /\ quant_extensional i /\
                    equivalent_args fuel xs ys)
          (ensures eval_args i xs rho == eval_args i ys rho)
          (decreases %[fuel; L.length xs + 1]) =
  match xs, ys with
  | x :: rest, y :: tail ->
    lemma_equivalent_sound fuel x y i rho;
    lemma_equivalent_args_sound fuel rest tail i rho
  | _, _ -> ()
