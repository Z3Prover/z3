module Z3NlaLemma

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native --fuel 1 --ifuel 1 --z3rlimit 10"

open FStar.Real
open FStar.List.Tot
module L = FStar.List.Tot
module P = Z3LinearArithmeticTheory

(* Ordered-ring refutations for incremental linearization. Search and
   factor selection are outside this kernel; no solver is called here. *)
type monomial = list nat
type poly = p:P.polynomial monomial{p.denom = 1}
type relation = | Equal | Nonzero | Nonnegative | Positive
type fact = { poly:poly; relation:relation }

#push-options "--using_facts_from 'Prims FStar.Real' --fuel 0 --ifuel 0"
let lemma_distribute (c d:int) (x y z:real)
  : Lemma (of_int (c * d) *. (x *. y) +. of_int c *. x *. z ==
           of_int c *. x *. (of_int d *. y +. z)) =
  P.lemma_of_int_product c d;
  assert ((of_int c *. of_int d) *. (x *. y) ==
          (of_int c *. x) *. (of_int d *. y));
  assert ((of_int c *. x) *. (of_int d *. y +. z) ==
          (of_int c *. x) *. (of_int d *. y) +. (of_int c *. x) *. z)

let lemma_expand (a b u v:real)
  : Lemma (u *. v +. (b *. u +. a *. (b +. v)) == (a +. u) *. (b +. v)) =
  assert ((a +. u) *. (b +. v) == a *. (b +. v) +. u *. (b +. v));
  assert (u *. (b +. v) == b *. u +. u *. v)

let lemma_cross_step (a b c:real)
  : Lemma (a *. c +. b *. c == (a +. b) *. c) = ()
#pop-options

let rec monomial_value (m:monomial) (rho:nat -> real)
  : Tot real (decreases m) =
  match m with [] -> 1.0R | x :: rest -> rho x *. monomial_value rest rho

let value (p:poly) (rho:nat -> real) : real = P.value p (fun m -> monomial_value m rho)

let holds (f:fact) (rho:nat -> real) : prop =
  let v = value f.poly rho in
  match f.relation with
  | Equal -> v == 0.0R
  | Nonzero -> ~(v == 0.0R)
  | Nonnegative -> v >=. 0.0R
  | Positive -> v >. 0.0R

let rec all_hold (fs:list fact) (rho:nat -> real) : Tot prop (decreases fs) =
  match fs with [] -> True | f :: rest -> holds f rho /\ all_hold rest rho

let rec merge (xs ys:monomial) : Tot monomial (decreases %[xs; ys]) =
  match xs, ys with
  | [], _ -> ys
  | _, [] -> xs
  | x :: rest, y :: tail ->
    if x <= y then x :: merge rest ys else y :: merge xs tail

let rec lemma_merge (xs ys:monomial) (rho:nat -> real)
  : Lemma (monomial_value (merge xs ys) rho ==
           monomial_value xs rho *. monomial_value ys rho)
          (decreases %[xs; ys]) =
  match xs, ys with
  | [], _ | _, [] -> ()
  | x :: rest, y :: tail ->
    if x <= y then (
      lemma_merge rest ys rho;
      assert (merge xs ys == x :: merge rest ys);
      assert (monomial_value xs rho == rho x *. monomial_value rest rho);
      assert (monomial_value (merge xs ys) rho == rho x *. monomial_value (merge rest ys) rho))
    else (
      lemma_merge xs tail rho;
      assert (merge xs ys == y :: merge xs tail);
      assert (monomial_value ys rho == rho y *. monomial_value tail rho);
      assert (monomial_value (merge xs ys) rho == rho y *. monomial_value (merge xs tail) rho))

let rec row (c:int) (m:monomial) (ys:list (int & monomial))
  : Tot (list (int & monomial)) (decreases ys) =
  match ys with [] -> [] | (d, n) :: rest -> (c * d, merge m n) :: row c m rest

let rec cross (xs ys:list (int & monomial))
  : Tot (list (int & monomial)) (decreases xs) =
  match xs with [] -> [] | (c, m) :: rest -> row c m ys @ cross rest ys

#push-options "--fuel 0 --ifuel 1"
let rec lemma_row (c:int) (m:monomial) (ys:list (int & monomial)) (rho:nat -> real)
  : Lemma (P.monomial_value (row c m ys) (fun m -> monomial_value m rho) ==
           of_int c *. monomial_value m rho *.
           P.monomial_value ys (fun m -> monomial_value m rho))
          (decreases ys) =
  let r = fun m -> monomial_value m rho in
  match ys with
  | [] ->
    assert_norm (row c m [] == []);
    assert_norm (P.monomial_value [] r == 0.0R)
  | (d, n) :: rest ->
    lemma_merge m n rho;
    lemma_row c m rest rho;
    assert_norm (row c m ((d, n) :: rest) == (c * d, merge m n) :: row c m rest);
    assert_norm (P.monomial_value ((d, n) :: rest) r ==
            of_int d *. r n +. P.monomial_value rest r);
    assert_norm (P.monomial_value ((c * d, merge m n) :: row c m rest) r ==
            of_int (c * d) *. r (merge m n) +.
            P.monomial_value (row c m rest) r);
    calc (==) {
      P.monomial_value (row c m ys) r;
      == {} of_int (c * d) *. monomial_value (merge m n) rho +.
        P.monomial_value (row c m rest) r;
      == {} of_int (c * d) *. (monomial_value m rho *. monomial_value n rho) +.
        of_int c *. monomial_value m rho *. P.monomial_value rest r;
      == { lemma_distribute c d (monomial_value m rho) (monomial_value n rho)
             (P.monomial_value rest r) }
        of_int c *. monomial_value m rho *.
          (of_int d *. monomial_value n rho +. P.monomial_value rest r);
      == {} of_int c *. monomial_value m rho *. P.monomial_value ys r;
    }

let rec lemma_cross (xs ys:list (int & monomial)) (rho:nat -> real)
  : Lemma (P.monomial_value (cross xs ys) (fun m -> monomial_value m rho) ==
           P.monomial_value xs (fun m -> monomial_value m rho) *.
           P.monomial_value ys (fun m -> monomial_value m rho))
          (decreases xs) =
  let r = fun m -> monomial_value m rho in
  match xs with
  | [] ->
    assert_norm (cross [] ys == []);
    assert_norm (P.monomial_value [] r == 0.0R)
  | (c, m) :: rest ->
    P.lemma_append (row c m ys) (cross rest ys) r;
    lemma_row c m ys rho;
    lemma_cross rest ys rho;
    assert_norm (cross ((c, m) :: rest) ys == row c m ys @ cross rest ys);
    assert_norm (P.monomial_value ((c, m) :: rest) r ==
            of_int c *. r m +. P.monomial_value rest r);
    calc (==) {
      P.monomial_value (cross xs ys) r;
      == {} P.monomial_value (row c m ys) r +. P.monomial_value (cross rest ys) r;
      == {} (of_int c *. monomial_value m rho) *. P.monomial_value ys r +.
        P.monomial_value rest r *. P.monomial_value ys r;
      == { lemma_cross_step (of_int c *. monomial_value m rho)
             (P.monomial_value rest r) (P.monomial_value ys r) }
        (of_int c *. monomial_value m rho +. P.monomial_value rest r) *.
          P.monomial_value ys r;
      == {} P.monomial_value xs r *. P.monomial_value ys r;
    }
#pop-options

[@@"opaque_to_smt"]
let multiply (p q:poly) : poly =
  let a : poly = { P.mono = cross p.mono q.mono; cst = 0; denom = 1 } in
  P.add a (P.add (P.scale q.cst 1 {p with cst = 0}) (P.scale p.cst 1 q))

#push-options "--fuel 0 --ifuel 0"
let lemma_multiply (p q:poly) (rho:nat -> real)
  : Lemma (value (multiply p q) rho == value p rho *. value q rho) =
  let r = fun m -> monomial_value m rho in
  let a : poly = { P.mono = cross p.mono q.mono; cst = 0; denom = 1 } in
  lemma_cross p.mono q.mono rho;
  P.lemma_scale q.cst 1 {p with cst = 0} r;
  P.lemma_scale p.cst 1 q r;
  P.lemma_add (P.scale q.cst 1 {p with cst = 0}) (P.scale p.cst 1 q) r;
  P.lemma_add a (P.add (P.scale q.cst 1 {p with cst = 0}) (P.scale p.cst 1 q)) r;
  let u = P.monomial_value p.mono r in
  let v = P.monomial_value q.mono r in
  assert (P.value a r == u *. v);
  assert (P.value {p with cst = 0} r == u);
  assert (value p rho == of_int p.cst +. u);
  assert (value q rho == of_int q.cst +. v);
  let b = P.scale q.cst 1 {p with cst = 0} in
  let c = P.scale p.cst 1 q in
  let d = P.add b c in
  assert_norm (multiply p q ==
    P.add { P.mono = cross p.mono q.mono; cst = 0; denom = 1 }
      (P.add (P.scale q.cst 1 {p with cst = 0}) (P.scale p.cst 1 q)));
  assert (P.value b r == of_int q.cst *. u);
  assert (P.value c r == of_int p.cst *. value q rho);
  assert (P.value d r == P.value b r +. P.value c r);
  assert (value (multiply p q) rho == P.value a r +. P.value d r);
  assert (value (multiply p q) rho ==
          u *. v +. (of_int q.cst *. u +. of_int p.cst *. value q rho));
  lemma_expand (of_int p.cst) (of_int q.cst) u v
#pop-options

let nonnegative (r:relation) : bool = r = Nonnegative || r = Positive
let nonzero (r:relation) : bool = r = Nonzero || r = Positive

let product_relation (a b:relation) : option relation =
  if a = Equal || b = Equal then Some Equal
  else if nonnegative a && nonnegative b
  then Some (if a = Positive && b = Positive then Positive else Nonnegative)
  else if nonzero a && nonzero b then Some Nonzero
  else None

let product (a b:fact) : option fact =
  match product_relation a.relation b.relation with
  | None -> None
  | Some r -> Some { poly = multiply a.poly b.poly; relation = r }

let lemma_product (a b f:fact) (rho:nat -> real)
  : Lemma (requires holds a rho /\ holds b rho /\ product a b == Some f)
          (ensures holds f rho) =
  lemma_multiply a.poly b.poly rho

let scale (c:int) (f:fact) : option fact =
  if c = 0 then Some { poly = P.zero; relation = Equal }
  else if nonnegative f.relation && c < 0 then None
  else Some { poly = P.scale c 1 f.poly; relation = f.relation }

let lemma_scale (c:int) (f g:fact) (rho:nat -> real)
  : Lemma (requires holds f rho /\ scale c f == Some g)
          (ensures holds g rho) =
  if c <> 0 then P.lemma_scale c 1 f.poly (fun m -> monomial_value m rho)

let add_relation (a b:relation) : option relation =
  if a = Equal then Some b
  else if b = Equal then Some a
  else if nonnegative a && nonnegative b
  then Some (if a = Positive || b = Positive then Positive else Nonnegative)
  else None

let add (a b:fact) : option fact =
  match add_relation a.relation b.relation with
  | None -> None
  | Some r -> Some { poly = P.add a.poly b.poly; relation = r }

let lemma_add (a b f:fact) (rho:nat -> real)
  : Lemma (requires holds a rho /\ holds b rho /\ add a b == Some f)
          (ensures holds f rho) =
  P.lemma_add a.poly b.poly (fun m -> monomial_value m rho)

let rec nth (#a:Type) (xs:list a) (i:nat) : Tot (option a) (decreases xs) =
  match xs with [] -> None | x :: rest -> if i = 0 then Some x else nth rest (i - 1)

let rec lemma_nth (fs:list fact) (i:nat) (f:fact) (rho:nat -> real)
  : Lemma (requires all_hold fs rho /\ nth fs i == Some f)
          (ensures holds f rho) (decreases fs) =
  match fs with [] -> () | _ :: rest -> if i <> 0 then lemma_nth rest (i - 1) f rho

let rec linear (prior:list fact) (terms:list (nat & int)) (acc:fact)
  : Tot (option fact) (decreases terms) =
  match terms with
  | [] -> Some acc
  | (i, c) :: rest ->
    (match nth prior i with
     | None -> None
     | Some f ->
       match scale c f with
       | None -> None
       | Some f -> match add acc f with None -> None | Some g -> linear prior rest g)

let rec lemma_linear (prior:list fact) (terms:list (nat & int)) (acc result:fact) (rho:nat -> real)
  : Lemma (requires all_hold prior rho /\ holds acc rho /\ linear prior terms acc == Some result)
          (ensures holds result rho) (decreases terms) =
  match terms with
  | [] -> ()
  | (i, c) :: rest ->
    let f = Some?.v (nth prior i) in
    let g = Some?.v (scale c f) in
    let h = Some?.v (add acc g) in
    lemma_nth prior i f rho;
    lemma_scale c f g rho;
    lemma_add acc g h rho;
    lemma_linear prior rest h result rho

type step =
  | Input : index:nat -> step
  | Product : left:nat -> right:nat -> step
  | ZeroProduct : index:nat -> argument:poly -> step
  | Square : argument:poly -> step
  | Linear : offset:nat -> terms:list (nat & int) -> step

let replay (inputs prior:list fact) (s:step) : option fact =
  match s with
  | Input i -> nth inputs i
  | Product i j ->
    (match nth prior i, nth prior j with Some a, Some b -> product a b | _, _ -> None)
  | ZeroProduct i p ->
    (match nth prior i with
     | Some f -> if f.relation = Equal then Some { poly = multiply f.poly p; relation = Equal } else None
     | _ -> None)
  | Square p -> Some { poly = multiply p p; relation = Nonnegative }
  | Linear n terms ->
    linear prior terms { poly = P.constant n 1; relation = if n = 0 then Equal else Positive }

let lemma_replay (inputs prior:list fact) (s:step) (f:fact) (rho:nat -> real)
  : Lemma (requires all_hold inputs rho /\ all_hold prior rho /\ replay inputs prior s == Some f)
          (ensures holds f rho) =
  match s with
  | Input i -> lemma_nth inputs i f rho
  | Product i j ->
    let a = Some?.v (nth prior i) in
    let b = Some?.v (nth prior j) in
    lemma_nth prior i a rho; lemma_nth prior j b rho; lemma_product a b f rho
  | ZeroProduct i p ->
    let a = Some?.v (nth prior i) in
    lemma_nth prior i a rho; lemma_multiply a.poly p rho
  | Square p -> lemma_multiply p p rho
  | Linear n terms ->
    lemma_linear prior terms
      { poly = P.constant n 1; relation = if n = 0 then Equal else Positive } f rho

let rec run (inputs prior:list fact) (steps:list step)
  : Tot (option (list fact)) (decreases steps) =
  match steps with
  | [] -> Some prior
  | s :: rest ->
    match replay inputs prior s with None -> None | Some f -> run inputs (prior @ [f]) rest

let rec lemma_append (fs:list fact) (f:fact) (rho:nat -> real)
  : Lemma (requires all_hold fs rho /\ holds f rho)
          (ensures all_hold (fs @ [f]) rho) (decreases fs) =
  match fs with [] -> () | _ :: rest -> lemma_append rest f rho

let rec lemma_run (inputs prior result:list fact) (steps:list step) (rho:nat -> real)
  : Lemma (requires all_hold inputs rho /\ all_hold prior rho /\ run inputs prior steps == Some result)
          (ensures all_hold result rho) (decreases steps) =
  match steps with
  | [] -> ()
  | s :: rest ->
    let f = Some?.v (replay inputs prior s) in
    lemma_replay inputs prior s f rho;
    lemma_append prior f rho;
    lemma_run inputs (prior @ [f]) result rest rho

let contradiction (f:fact) : bool =
  P.all_zero (P.collect f.poly.mono []) &&
  (match f.relation with
   | Equal -> f.poly.cst <> 0
   | Nonzero -> f.poly.cst = 0
   | Nonnegative -> f.poly.cst < 0
   | Positive -> f.poly.cst <= 0)

let lemma_contradiction (f:fact) (rho:nat -> real)
  : Lemma (requires contradiction f /\ holds f rho) (ensures False) =
  P.lemma_collect f.poly.mono [] (fun m -> monomial_value m rho);
  P.lemma_all_zero (P.collect f.poly.mono []) (fun m -> monomial_value m rho)

let check (inputs:list fact) (steps:list step) (root:nat) : bool =
  match run inputs [] steps with
  | None -> false
  | Some fs -> match nth fs root with None -> false | Some f -> contradiction f

let check_sound (inputs:list fact) (steps:list step) (root:nat) (rho:nat -> real)
  : Lemma (requires all_hold inputs rho /\ check inputs steps root)
          (ensures False) =
  let fs = Some?.v (run inputs [] steps) in
  let f = Some?.v (nth fs root) in
  lemma_run inputs [] fs steps rho;
  lemma_nth fs root f rho;
  lemma_contradiction f rho
