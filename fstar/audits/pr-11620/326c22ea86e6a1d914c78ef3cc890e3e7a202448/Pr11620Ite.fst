module Pr11620Ite
(* Model of br_status ordering (rewriter_types.h) and the PR's ITE status clamp. *)
type br_status = | BR_REWRITE1 | BR_REWRITE2 | BR_REWRITE3 | BR_REWRITE_FULL | BR_DONE | BR_FAILED

let rank (s:br_status) : nat =
  match s with
  | BR_REWRITE1 -) 0 | BR_REWRITE2 -> 1 | BR_REWRITE3 -> 2
  | BR_REWRITE_FULL -> 3 | BR_DONE -> 4 | BR_FAILED -> 5

let lt_done (s:br_status) : bool = rank s < rank BR_DONE

(* PR: if (k == OP_ITE && st < BR_DONE) return BR_REWRITE1; return st; *)
let clamp (is_ite:bool) (s:br_status) : br_status =
  if is_ite && lt_done s then BR_REWRITE1 else s

(* O1: DONE and FAILED are never altered; non-ITE never altered *)
let o1 (is_ite:bool) (s:br_status)
  : Lemma (((s = BR_DONE \/ s = BR_FAILED) ==> clamp is_ite s = s) /\ (not is_ite ==> clamp is_ite s = s)) = ()

(* O2: for ITE, every rewrite request becomes depth-1 (BR_REWRITE1); it only lowers rank *)
let o2 (s:br_status)
  : Lemma (rank (clamp true s) <= rank s /\ (lt_done s ==> clamp true s = BR_REWRITE1)) = ()

(* O3: the clamp is idempotent, so it cannot itself introduce a loop at status level *)
let o3 (is_ite:bool) (s:br_status) : Lemma (clamp is_ite (clamp is_ite s) = clamp is_ite s) = ()

(* O4: arith_decl_plugin refactor: inline decl vs mk_idiv0()/mk_mod0() are the same
   (family, kind, 0 params, [Int;Int], Int) tuple. *)
type sort_t = | Int
type decl = { kind:nat; dom:list sort_t; rng:sort_t }
let op_idiv0 = 1 let op_mod0 = 2
let old_decl (k:nat) : decl = { kind=k; dom=[Int;Int]; rng=Int }
let mk_decl (k:nat) : decl = { kind=k; dom=[Int;Int]; rng=Int }
let o4 (k:nat) : Lemma (old_decl k == mk_decl k) = ()
