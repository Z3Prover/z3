(*
   Z3ValueTheory.fst

   Legacy concrete values for existing unindexed interpretations and
   soundness proofs. Deprecated as a foundation for new SMT semantics:
   use Z3DatatypeValue with sort-indexed carriers such as Z3TypedRoot.

   Operator tags live in Z3OperatorTags. The aliases below preserve
   existing clients; tag-only consumers should import that module directly.
   The legacy datatype remains unchanged until its proof clients migrate.
*)
module Z3ValueTheory
open Z3AstTheory

(* ----------------------------------------------------------------- *)
(* A concrete semantic domain covering every theory exercised here:    *)
(* Int/Bool (arith/bool), an array from Int to Int                     *)
(* (`Z3ArrayTheory.arr int int`, matching SMT-LIB's `(Array Int Int)`), *)
(* a sequence of Int (`Z3SeqTheory.seq int`, matching `(Seq Int)`), and *)
(* a 32-bit bitvector (`Z3BvTheory.bv 32`). Kept at `int`/`int`         *)
(* element/index types for the legacy unindexed contracts. This is   *)
(* not the compositional SMT carrier: the sort-indexed datatype/value *)
(* framework and Z3TypedRoot supply that separate semantic family.     *)
(* Generic sequence operations and semantic arrays accept arbitrary   *)
(* element types without requiring executable equality on functions.  *)
(* ----------------------------------------------------------------- *)

noeq
type value =
  | VInt  : int -> value
  | VBool : bool -> value
  | VArr  : Z3ArrayTheory.arr int int -> value
  | VSeq  : Z3SeqTheory.seq int -> value
  | VBV   : Z3BvTheory.bv 32 -> value

(* Compatibility aliases for the carrier-independent transport tags. *)
let op_not : decl_kind = Z3OperatorTags.op_not
let op_plus : decl_kind = Z3OperatorTags.op_plus
let op_select : decl_kind = Z3OperatorTags.op_select
let op_store : decl_kind = Z3OperatorTags.op_store
let op_bvand : decl_kind = Z3OperatorTags.op_bvand
let op_concat : decl_kind = Z3OperatorTags.op_concat
(* Polymorphic equality; its semantics are supplied by model contracts. *)
let op_eq : decl_kind = Z3OperatorTags.op_eq

(* Boolean constants and integer/bit-vector numerals. *)
let op_true : decl_kind = Z3OperatorTags.op_true
let op_false : decl_kind = Z3OperatorTags.op_false
let op_num_int : decl_kind = Z3OperatorTags.op_num_int
let op_num_bv : decl_kind = Z3OperatorTags.op_num_bv

(* Singleton sequence construction. *)
let op_seq_unit : decl_kind = Z3OperatorTags.op_seq_unit

(* Boolean connective tags; consumers check declaration arities and sorts. *)
let op_and : decl_kind = Z3OperatorTags.op_and
let op_or : decl_kind = Z3OperatorTags.op_or
let op_implies : decl_kind = Z3OperatorTags.op_implies

(* Proof-only observational equivalence, not an executable Boolean op. *)
let op_oeq : decl_kind = Z3OperatorTags.op_oeq

let op_mul : decl_kind = Z3OperatorTags.op_mul
let op_array_ext : decl_kind = Z3OperatorTags.op_array_ext
let op_ite : decl_kind = Z3OperatorTags.op_ite
let op_xor : decl_kind = Z3OperatorTags.op_xor
let op_distinct : decl_kind = Z3OperatorTags.op_distinct
let op_num_rational : decl_kind = Z3OperatorTags.op_num_rational
let op_arith_add : decl_kind = Z3OperatorTags.op_arith_add
let op_arith_mul : decl_kind = Z3OperatorTags.op_arith_mul
let op_arith_sub : decl_kind = Z3OperatorTags.op_arith_sub
let op_arith_div : decl_kind = Z3OperatorTags.op_arith_div
let op_arith_le : decl_kind = Z3OperatorTags.op_arith_le
let op_arith_lt : decl_kind = Z3OperatorTags.op_arith_lt
let op_arith_ge : decl_kind = Z3OperatorTags.op_arith_ge
let op_arith_gt : decl_kind = Z3OperatorTags.op_arith_gt
let op_to_real : decl_kind = Z3OperatorTags.op_to_real
let op_const_array : decl_kind = Z3OperatorTags.op_const_array
