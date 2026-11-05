module Z3List

(* Replacements for FStar.List.Tot functions on lists whose length grows with the
   input proof.  Under Cherry, List.Tot's map, filter and append use one C stack
   frame per element, and its higher-order functions call their argument through
   a closure (FStarLang/FStar#4815).  These versions are tail recursive, and
   [@@@monomorphize] specializes them on lambda arguments.  Each is proved equal to
   its List.Tot counterpart; the SMT patterns let callers' proofs keep reasoning
   about List.Tot. *)

module L = FStar.List.Tot

let rec lemma_rev_acc (#a:Type) (xs acc:list a)
  : Lemma (ensures L.rev_acc xs acc == L.append (L.rev xs) acc) (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest ->
    lemma_rev_acc rest (x :: acc);
    lemma_rev_acc rest [x];
    L.append_assoc (L.rev rest) [x] acc

let lemma_rev_cons (#a:Type) (x:a) (acc:list a)
  : Lemma (L.rev (x :: acc) == L.append (L.rev acc) [x]) =
  lemma_rev_acc acc [x]

let rec map_acc (#a #b:Type) ([@@@FStar.Attributes.monomorphize] f:a -> b)
                (xs:list a) (acc:list b)
  : Tot (list b) (decreases xs) =
  match xs with
  | [] -> L.rev acc
  | x :: rest -> map_acc f rest (f x :: acc)

let rec lemma_map_acc (#a #b:Type) (f:a -> b) (xs:list a) (acc:list b)
  : Lemma (ensures map_acc f xs acc == L.append (L.rev acc) (L.map f xs)) (decreases xs) =
  match xs with
  | [] -> L.append_l_nil (L.rev acc)
  | x :: rest ->
    lemma_map_acc f rest (f x :: acc);
    lemma_rev_cons (f x) acc;
    L.append_assoc (L.rev acc) [f x] (L.map f rest)

[@@FStar.Attributes.custard_inline]
let map (#a #b:Type) ([@@@FStar.Attributes.monomorphize] f:a -> b) (xs:list a) : list b =
  map_acc f xs []

let lemma_map (#a #b:Type) (f:a -> b) (xs:list a)
  : Lemma (map f xs == L.map f xs) [SMTPat (map f xs)] =
  lemma_map_acc f xs []

let rec filter_acc (#a:Type) ([@@@FStar.Attributes.monomorphize] f:a -> bool)
                   (xs:list a) (acc:list a)
  : Tot (list a) (decreases xs) =
  match xs with
  | [] -> L.rev acc
  | x :: rest -> if f x then filter_acc f rest (x :: acc) else filter_acc f rest acc

let rec lemma_filter_acc (#a:Type) (f:a -> bool) (xs acc:list a)
  : Lemma (ensures filter_acc f xs acc == L.append (L.rev acc) (L.filter f xs)) (decreases xs) =
  match xs with
  | [] -> L.append_l_nil (L.rev acc)
  | x :: rest ->
    if f x then (
      lemma_filter_acc f rest (x :: acc);
      lemma_rev_cons x acc;
      L.append_assoc (L.rev acc) [x] (L.filter f rest))
    else lemma_filter_acc f rest acc

[@@FStar.Attributes.custard_inline]
let filter (#a:Type) ([@@@FStar.Attributes.monomorphize] f:a -> bool) (xs:list a) : list a =
  filter_acc f xs []

let lemma_filter (#a:Type) (f:a -> bool) (xs:list a)
  : Lemma (filter f xs == L.filter f xs) [SMTPat (filter f xs)] =
  lemma_filter_acc f xs []

[@@FStar.Attributes.custard_inline]
let append (#a:Type) (xs ys:list a) : list a =
  L.rev_acc (L.rev xs) ys

let lemma_append (#a:Type) (xs ys:list a)
  : Lemma (append xs ys == L.append xs ys) [SMTPat (append xs ys)] =
  lemma_rev_acc (L.rev xs) ys;
  L.rev_involutive xs

let rec for_all (#a:Type) ([@@@FStar.Attributes.monomorphize] f:a -> bool) (xs:list a)
  : Tot bool (decreases xs) =
  match xs with
  | [] -> true
  | x :: rest -> if f x then for_all f rest else false

let rec lemma_for_all (#a:Type) (f:a -> bool) (xs:list a)
  : Lemma (ensures for_all f xs == L.for_all f xs) (decreases xs) [SMTPat (for_all f xs)] =
  match xs with
  | [] -> ()
  | _ :: rest -> lemma_for_all f rest

let rec existsb (#a:Type) ([@@@FStar.Attributes.monomorphize] f:a -> bool) (xs:list a)
  : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | x :: rest -> if f x then true else existsb f rest

let rec lemma_existsb (#a:Type) (f:a -> bool) (xs:list a)
  : Lemma (ensures existsb f xs == L.existsb f xs) (decreases xs) [SMTPat (existsb f xs)] =
  match xs with
  | [] -> ()
  | _ :: rest -> lemma_existsb f rest
