(*
   Z3ArrayInterp.fst

   The array theory's thin, `value`-level companion to
   `Z3ArrayTheory.fst`: wraps `Z3ArrayTheory.select`/`Z3ArrayTheory.store`
   (which only ever talk about `int`/`int` arrays) into the shared
   `Z3ValueTheory.value` domain, and exposes a single `interp_app :
   decl_kind -> list value -> option value` entry point that
   `Z3InterpretedProofChecker.fst`'s top-level dispatcher tries first.
   Returning `None` (rather than some fallback `value`) for any
   `decl_kind` this theory does not own is exactly what lets the
   top-level dispatcher fall through to the next theory in turn.

   Kept separate from `Z3ArrayTheory.fst` itself (rather than adding
   `interp_app` there directly) so `Z3ArrayTheory.fst` stays a pure
   `arr`/`select`/`store`-plus-lemmas module with no notion of
   `value`/`decl_kind` at all -- `value` is defined over `arr`, so a
   module *defining* `arr` cannot also depend on `value` without a
   circular module dependency.
*)
module Z3ArrayInterp
open Z3AstTheory
open Z3ValueTheory

let interp_select (args:list value) : value =
  match args with
  | [VArr a; VInt i] -> VInt (Z3ArrayTheory.select a i)
  | _ -> VInt 0

let interp_store (args:list value) : value =
  match args with
  | [VArr a; VInt i; VInt x] -> VArr (Z3ArrayTheory.store a i x)
  | _ -> VInt 0

(* The array theory's dispatcher: `Some v` for any `decl_kind` it owns
   (`op_select`/`op_store`), `None` for everything else, so the caller
   can fall through to the next theory. `int_params` (a numeral
   literal's raw payload, e.g. for `op_num_int`/`op_num_bv`) is
   threaded through uniformly across every theory's `interp_app` even
   though the array theory itself never needs it, so every theory
   shares one dispatch signature. *)
let interp_app (k:decl_kind) (int_params:list int) (args:list value) : option value =
  if k = op_select then Some (interp_select args)
  else if k = op_store then Some (interp_store args)
  else None
