module Z3QuantifierVacuitySyntax

open Z3AstTheory
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

let lemma_lower_sort (cutoff:nat) (e result:expr)
  : Lemma (requires lower cutoff e == Some result)
          (ensures get_sort e == get_sort result) =
  match e with Var _ _ | App _ _ | Quantifier _ _ _ _ -> ()

let quantified (k:quantifier_kind) (bs:list sort) (body:expr) : expr =
  if bs = [] then body else Quantifier k bs bool_sort body

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

let rec first_removal (remaining:nat) (n:nat) (e:expr)
  : Tot (option expr) (decreases remaining) =
  if remaining = 0 then None
  else match remove n e with
  | Some b -> Some b
  | None -> first_removal (remaining - 1) (n + 1) e

let step (e:expr) : option expr =
  match e with Quantifier _ bs _ _ -> first_removal (L.length bs) 0 e | _ -> None

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

