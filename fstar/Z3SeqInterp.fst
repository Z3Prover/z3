(*
   Z3SeqInterp.fst

   The sequence theory's thin, `value`-level companion to
   `Z3SeqTheory.fst`, mirroring `Z3ArrayInterp.fst`'s role for arrays:
   wraps `Z3SeqTheory.concat` into the shared `Z3ValueTheory.value`
   domain and exposes `interp_app : decl_kind -> list value -> option
   value`, owning exactly `op_concat`.
*)
module Z3SeqInterp
open Z3AstTheory
open Z3ValueTheory

let interp_concat (args:list value) : value =
  match args with
  | [VSeq a; VSeq b] -> VSeq (Z3SeqTheory.concat a b)
  | _ -> VInt 0

let interp_seq_unit (args:list value) : value =
  match args with
  | [VInt x] -> VSeq (Z3SeqTheory.unit x)
  | _ -> VInt 0

(* `int_params` is threaded through for uniformity with the other
   theories' `interp_app` (e.g. `Z3BvInterp.fst`'s `op_num_bv` needs
   it); the seq theory itself never does. *)
let interp_app (k:decl_kind) (int_params:list int) (args:list value) : option value =
  if k = op_concat then Some (interp_concat args)
  else if k = op_seq_unit then Some (interp_seq_unit args)
  else None
