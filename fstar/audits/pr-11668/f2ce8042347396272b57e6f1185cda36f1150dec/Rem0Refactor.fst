module Rem0Refactor
(* Model: a func_decl built by mk_func_decl(family, op, 2 Int domain, Int range) is a record
   determined by these fields; mk_func_decl is a deterministic (hash-consed) constructor. *)
type op = | OP_REM | OP_MOD | OP_MOD0 | OP_OTHER
type sort = | Int
type decl = { fam:nat; o:op; dom:list sort; rng:sort }
let arith_family : nat = 1
let mk_func_decl (o:op) (dom:list sort) (rng:sort) : decl = {fam=arith_family; o; dom; rng}
let mk_int = Int
(* base inline code *)
let old_branch () : decl = let rs = [mk_int; mk_int] in mk_func_decl OP_MOD0 rs mk_int
(* helper in arith_util::mk_rem0 (unchanged by PR) *)
let mk_rem0 () : decl = let rs = [mk_int; mk_int] in mk_func_decl OP_MOD0 rs mk_int
(* guard is untouched: same branch condition; result equal *)
let partial_rem (f_is_rem:bool) (n:nat) (arg1_numeral:bool) (use_new:bool) : option decl =
  if f_is_rem && n = 2 && not arg1_numeral then Some (if use_new then mk_rem0 () else old_branch ()) else None
let equiv (b:bool) (n:nat) (c:bool) : Lemma (partial_rem b n c true == partial_rem b n c false) = ()
(* helper identical to mk_mod0 (and to OP_MOD0 decl used by is_rem0/is_mod0) *)
let same_as_mod0 () : Lemma (mk_rem0 () == (let rs=[mk_int;mk_int] in mk_func_decl OP_MOD0 rs mk_int)) = ()
let sort_ok () : Lemma ((mk_rem0 ()).dom == [Int;Int] /\ (mk_rem0 ()).rng == Int /\ (mk_rem0 ()).o == OP_MOD0) = ()
