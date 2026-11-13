module PR11677MonomialBounds
(* Semantic model of PR 11677 guards in monomial_bounds.cpp.
   root_orig is an abstract total function standing for rational::root; no axioms. *)

let max_bits : nat = 256
let max_factors : nat = 256

(* Obligation 1: bounded_root *)
let bounded_root (root_orig: int -> nat -> option int) (bits_a: nat) (a: int) (p: nat) : option int =
  if p > 1 && (p > max_factors || bits_a > max_bits) then None
  else root_orig a p

(* result is either abstention or exactly the original root *)
let ob1_refines (root_orig: int -> nat -> option int) (bits_a: nat) (a: int) (p: nat)
  : Lemma (match bounded_root root_orig bits_a a p with
           | None -> p > 1 /\ (p > max_factors \/ bits_a > max_bits) \/ root_orig a p == None
           | Some r -> root_orig a p == Some r)
  = ()

(* first-power roots are never skipped *)
let ob1_first_power (root_orig: int -> nat -> option int) (bits_a: nat) (a: int)
  : Lemma (bounded_root root_orig bits_a a 1 == root_orig a 1) = ()

(* sizes at the boundary: 256 bits and 256 factors are still processed *)
let ob1_boundary (root_orig: int -> nat -> option int) (a: int)
  : Lemma (bounded_root root_orig 256 a 256 == root_orig a 256 /\
           bounded_root root_orig 257 a 2 == None /\
           bounded_root root_orig 0 a 257 == None) = ()

(* Obligation 2: tighten_lp guard. A monic is a list of per-variable bit sizes. *)
let rec all_small (l: list nat) : bool =
  match l with [] -> true | b :: t -> b <= max_bits && all_small t

let tighten_guard_ok (nfactors: nat) (bits: list nat) : bool =
  nfactors <= max_factors && all_small bits

(* skipped (guard false) => returns false = no bound; otherwise body runs unchanged *)
let tighten_lp (body: bool) (nfactors: nat) (bits: list nat) : bool =
  if tighten_guard_ok nfactors bits then body else false

let ob2_sound (body: bool) (n: nat) (bits: list nat)
  : Lemma ((tighten_lp body n bits ==> body) /\
           (tighten_guard_ok n bits ==> tighten_lp body n bits == body)) = ()

let rec all_small_mem (l: list nat) (x: nat)
  : Lemma (requires all_small l /\ List.Tot.memP x l) (ensures x <= max_bits) =
  match l with [] -> () | h :: t -> if h = x then () else all_small_mem t x

(* Obligation 3: check_monic / is_linear reordering, both pure predicates *)
let old_skip (lin chk: bool) = chk || not lin
let new_skip (lin chk: bool) = not lin || chk
let ob3_equiv (lin chk: bool) : Lemma (old_skip lin chk == new_skip lin chk) = ()
(* gain: check_monic is evaluated only when linear *)
let ob3_check_only_if_linear (lin: bool) : Lemma (not lin ==> new_skip lin true == true /\ new_skip lin false == true) = ()
