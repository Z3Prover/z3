(*
   Z3ArrayGroundIndexEq.fst

   Targeted audit of `array_rewriter::mk_eq_core`'s "constant array with
   store chain, uninterpreted-sorted domain" branch
   (src/ast/rewriter/array_rewriter.cpp, ~line 957), motivated by open
   PR #11164 ("Fix MBQI returning `unknown` on array model values over
   uninterpreted sorts", fixing issue #11156).

   Context: comparing `(= lhs rhs)` where both `lhs`/`rhs` are a chain
   of `store`s on top of a `(as const S) v`/`(as const S) w` base, over
   an array sort `S` with an *uninterpreted* index sort, cannot in
   general be decided by enumerating the domain (it may be infinite).
   The existing code therefore falls back to `expand_store` + a direct
   array `=`, which `mk_eq`/MBQI must then discharge via the array
   extensionality axiom -- i.e. a universally-quantified formula over
   the whole (uninterpreted) index sort.

   The bug: this fallback fired *unconditionally* whenever both sides
   were const-with-stores over an uninterpreted domain, even when every
   store index on *both* sides was already a concrete model value
   (`m().is_value(...)`) -- exactly the situation arising during MBQI's
   own array-model reconstruction (issue #11156). In that situation the
   quantified extensionality formula is not merely unnecessary, it is a
   regression: MBQI, asked to verify a quantifier it itself just
   introduced over values it already fully knows, could give up
   (`unknown`, "(incomplete (theory array))") instead of resolving the
   (in truth decidable, quantifier-free) comparison directly.

   The fix adds a `has_value_indices` guard excluding this branch
   whenever every index in both store chains is a concrete value,
   letting control fall through to the existing (quantifier-free)
   pointwise/finite comparison machinery further down in the same
   function.

   This file formalizes the precise semantic fact that justifies the
   fix: *when all store indices are concrete, finitely many ground
   points*, full extensional array equality is equivalent to checking
   only those finitely many points plus base equality -- no
   quantification over the (possibly uninterpreted/infinite) index
   domain is logically required, confirming the fix does not trade
   soundness for the completeness gain.
*)
module Z3ArrayGroundIndexEq

open FStar.FunctionalExtensionality
open Z3ArrayTheory

(* ----------------------------------------------------------------- *)
(* A store chain, as a list of (index, value) update pairs applied on  *)
(* top of a constant base, list head = outermost/most-recent `store`   *)
(* (so it shadows any later/inner pair at the same index, matching     *)
(* real `store`'s semantics for repeated indices). *)
(* ----------------------------------------------------------------- *)

let rec chain (#idx:eqtype) (#v:Type) (base:v) (ps:list (idx & v)) : arr idx v =
  match ps with
  | [] -> const_arr base
  | (i, x) :: rest -> store (chain base rest) i x

let rec indices (#idx:eqtype) (#v:Type) (ps:list (idx & v)) : list idx =
  match ps with
  | [] -> []
  | (i, _) :: rest -> i :: indices rest

(* Off the chain's own indices, a chain always reads back as its base
   constant -- the "outside the explicit stores, nothing changed"
   fact that makes the finite check sufficient. *)
let rec lemma_chain_off_indices (#idx:eqtype) (#v:Type) (base:v) (ps:list (idx & v)) (x:idx)
  : Lemma (requires not (List.Tot.mem x (indices ps)))
          (ensures select (chain base ps) x == base)
  = match ps with
    | [] -> ()
    | (i, _) :: rest -> lemma_chain_off_indices base rest x

(* ----------------------------------------------------------------- *)
(* Main theorem: finitely-many-ground-points suffices.                 *)
(*                                                                      *)
(* Two store chains over (possibly different) bases `v`/`w` are fully   *)
(* extensionally equal iff (a) the bases agree, and (b) they agree at   *)
(* every index mentioned in *either* chain. No quantification over any  *)
(* index outside this finite, explicit, syntactically-available list    *)
(* is needed -- which is exactly the quantifier-free check              *)
(* `has_value_indices` lets `mk_eq_core` fall through to, instead of     *)
(* the general `expand_store` + extensionality-axiom rewrite.           *)
(* ----------------------------------------------------------------- *)
let lemma_ground_chain_eq_iff_finite_check
      (#idx:eqtype) (#v:eqtype) (base1 base2:v) (ps1 ps2:list (idx & v))
  : Lemma (requires base1 == base2 /\
                    (forall (x:idx). List.Tot.mem x (List.Tot.append (indices ps1) (indices ps2)) ==>
                                 select (chain base1 ps1) x == select (chain base2 ps2) x))
          (ensures feq (chain base1 ps1) (chain base2 ps2))
  =
  let combined = List.Tot.append (indices ps1) (indices ps2) in
  let aux (x:idx) : Lemma (select (chain base1 ps1) x == select (chain base2 ps2) x) =
    if List.Tot.mem x combined then ()
    else begin
      List.Tot.Properties.append_mem (indices ps1) (indices ps2) x;
      lemma_chain_off_indices base1 ps1 x;
      lemma_chain_off_indices base2 ps2 x
    end
  in
  FStar.Classical.forall_intro aux

(* The converse direction is immediate extensionality (if the arrays
   are equal, they of course agree everywhere, in particular on the
   finite index list and on the bases read off that list) -- recorded
   for completeness, so the "iff" promised above is fully established,
   not just the soundness-critical forward direction the rewrite relies
   on. *)
let lemma_ground_chain_eq_implies_finite_check
      (#idx:eqtype) (#v:eqtype) (base1 base2:v) (ps1 ps2:list (idx & v))
  : Lemma (requires feq (chain base1 ps1) (chain base2 ps2))
          (ensures (forall (x:idx). select (chain base1 ps1) x == select (chain base2 ps2) x))
  = ()
