module Z3FiniteSetLocalRewrites
(* Semantic model of PR 11511 bounded_filter_cfg::bounded/find_value/is_extremum.
   Finite sets are lists; elements are ints (a representative ordered sort). *)
open FStar.List.Tot

let all_in (s: list int) (p: int -> bool) : bool = for_all p s
let some_in (s: list int) (p: int -> bool) : bool = existsb p s
let is_set_empty (s: list int) : bool = Nil? s
(* filter(lambda x. p, s) = s  <=> all_in; filter(...) = empty <=> not some_in *)

(* Obligation 1: find_value fixed point.  forall: S=empty \/ (S={t} /\ body t);
   exists: not (t in S /\ body t).  Body is x==t /\ r(x). *)
let singleton_eq (s: list int) (t: int) : prop = forall (x:int). memP x s <==> x == t

val ob1_forall : s:list int -> t:int -> r:(int -> bool) ->
  Lemma (all_in s (fun x -> x = t && r x) ==
         (Nil? s || ((forall (x:int). memP x s ==> x == t) && (memP t s ==> r t))))
let rec ob1_forall s t r = match s with
  | [] -> ()
  | h :: tl -> ob1_forall tl t r

val ob1_forall_prop : s:list int -> t:int -> r:(int -> bool) ->
  Lemma (requires all_in s (fun x -> x = t && r x))
        (ensures (Nil? s \/ (singleton_eq s t /\ r t)))
let rec ob1_forall_prop s t r = match s with
  | [] -> ()
  | h :: tl -> if Nil? tl then () else ob1_forall_prop tl t r

val ob1_forall_conv : s:list int -> t:int -> r:(int -> bool) ->
  Lemma (requires (Nil? s \/ (singleton_eq s t /\ r t)))
        (ensures all_in s (fun x -> x = t && r x))
let rec ob1_forall_conv s t r = match s with
  | [] -> ()
  | h :: tl -> assert (memP h s); ob1_forall_conv tl t r

val ob1_exists : s:list int -> t:int -> r:(int -> bool) ->
  Lemma (some_in s (fun x -> x = t && r x) == (memP t s && r t))
let rec ob1_exists s t r = match s with
  | [] -> ()
  | h :: tl -> ob1_exists tl t r

(* Bound pair: x<=b /\ x>=b implies x==b, so the point is b. *)
val ob1_bounds : x:int -> b:int -> Lemma (requires x <= b /\ x >= b) (ensures x == b)
let ob1_bounds x b = ()

(* Obligation 2: is_extremum. Nonempty finite set has an element whose projection is
   maximal (<=) / minimal (>=); hence exists-filter is empty iff S is empty. *)
val has_max : s:list int -> proj:(int -> int) ->
  Lemma (requires Cons? s)
        (ensures (exists (x:int). memP x s /\ (forall (y:int). memP y s ==> proj y <= proj x)))
let rec has_max s proj = match s with
  | [h] -> ()
  | h :: tl ->
    has_max tl proj;
    FStar.Classical.exists_elim
      (exists (x:int). memP x s /\ (forall (y:int). memP y s ==> proj y <= proj x))
      #_ #(fun x -> memP x tl /\ (forall (y:int). memP y tl ==> proj y <= proj x))
      ()
      (fun x -> if proj h <= proj x then () else assert (forall (y:int). memP y s ==> proj y <= proj h))

val has_min : s:list int -> proj:(int -> int) ->
  Lemma (requires Cons? s)
        (ensures (exists (x:int). memP x s /\ (forall (y:int). memP y s ==> proj y >= proj x)))
let rec has_min s proj = match s with
  | [h] -> ()
  | h :: tl ->
    has_min tl proj;
    FStar.Classical.exists_elim
      (exists (x:int). memP x s /\ (forall (y:int). memP y s ==> proj y >= proj x))
      #_ #(fun x -> memP x tl /\ (forall (y:int). memP y tl ==> proj y >= proj x))
      ()
      (fun x -> if proj h >= proj x then () else assert (forall (y:int). memP y s ==> proj y >= proj h))

(* Conversely an empty set has no witness, so (exists x in S. extremum x) <=> S nonempty. *)
val ext_empty : proj:(int -> int) ->
  Lemma (~ (exists (x:int). memP x ([] <: list int)))
let ext_empty proj = ()

(* Obligation 3: independent-guard splitting; d does not depend on the bound variable. *)
val ob3_forall_or : s:list int -> d:bool -> r:(int -> bool) ->
  Lemma (all_in s (fun x -> d || r x) == (d || all_in s r))
let rec ob3_forall_or s d r = match s with
  | [] -> ()
  | h :: tl -> ob3_forall_or tl d r

val ob3_exists_and : s:list int -> d:bool -> r:(int -> bool) ->
  Lemma (some_in s (fun x -> d && r x) == (d && some_in s r))
let rec ob3_exists_and s d r = match s with
  | [] -> ()
  | h :: tl -> ob3_exists_and tl d r

val ob3_forall_implies : s:list int -> g:bool -> c:(int -> bool) ->
  Lemma (all_in s (fun x -> (not g) || c x) == ((not g) || all_in s c))
let ob3_forall_implies s g c = ob3_forall_or s (not g) c

(* No-bound-variable case: forall x in S. c  <=> S=empty \/ c ; exists <=> S<>empty /\ c *)
val ob3_const : s:list int -> c:bool ->
  Lemma (all_in s (fun _ -> c) == (Nil? s || c) /\ some_in s (fun _ -> c) == (Cons? s && c))
let rec ob3_const s c = match s with | [] -> () | h :: tl -> ob3_const tl c
