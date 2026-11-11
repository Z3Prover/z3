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
(* element/index types for the legacy example interpretation. This is *)
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

(* `decl_kind` is `int` (`Z3AstTheory.fst`); these are the handful of
   interpreted operators this project gives real semantics to. Every
   other symbol used by the example leaves (named constants like `a`,
   `i`, `v`, `x`, `y`, ...) stays uninterpreted. Each constant is
   "owned" by exactly one theory's `interp_app` (array: `op_select`/
   `op_store`; seq: `op_concat`; bv: `op_bvand`/`op_num_bv`; the
   remaining "core" bool/arith/`eq`/literal ops --
   `op_not`/`op_plus`/`op_eq`/`op_true`/`op_false`/`op_num_int` --
   have no dedicated theory file of their own, so they stay directly
   in `Z3InterpretedProofChecker.fst`). *)
let op_not : decl_kind = Z3OperatorTags.op_not
let op_plus : decl_kind = Z3OperatorTags.op_plus
let op_select : decl_kind = Z3OperatorTags.op_select
let op_store : decl_kind = Z3OperatorTags.op_store
let op_bvand : decl_kind = Z3OperatorTags.op_bvand
let op_concat : decl_kind = Z3OperatorTags.op_concat
(* Polymorphic equality (any sort `s`, `domain = [s;s]`, `range = Bool`).
   Added together with the injective-naming fix below so an `eq_symm`
   rewrite matcher can be proved sound without any new model axioms. *)
let op_eq : decl_kind = Z3OperatorTags.op_eq

(* Literal constants: `true`/`false` (`OP_TRUE`/`OP_FALSE`) and
   0-ary numeral applications (`OP_NUM`-family: `Z3_mk_int`/
   `Z3_mk_numeral`, bit-vector numerals, ...). Added so `provably_distinct`
   (`Z3PatternMatchedProofChecker.fst`) can discriminate *literal*
   constants by their actual decoded value rather than by the
   (sort-restricted, Int-only) injective-naming trick `uninterp_app`
   already relies on for free/symbolic 0-ary constants (the naming
   trick is only sound for an *infinite* sort; `Bool`/`BVn` are
   finite, so two differently-*named* Bool/BV constants can never be
   assumed pairwise distinct, but two differently-*valued* Bool/BV
   *literals* always are). A numeral's literal value is carried in
   `func_decl.int_params` (already used by `re.loop`'s bounds), one
   element: `[v]`. *)
let op_true : decl_kind = Z3OperatorTags.op_true
let op_false : decl_kind = Z3OperatorTags.op_false
let op_num_int : decl_kind = Z3OperatorTags.op_num_int
let op_num_bv : decl_kind = Z3OperatorTags.op_num_bv

(* `seq.unit`: wraps a single `Int` element into the length-1
   sequence containing it (`Z3SeqTheory.unit`). Added so that
   `is_unique_value` (`Z3PatternMatchedProofChecker.fst`) can
   recognize sequence *literals* -- i.e. values built purely from
   `seq.unit`/`op_concat` applied to unique-value elements, with no
   uninterpreted sub-term anywhere -- as themselves unique values,
   mirroring how `op_num_int`/`op_num_bv`/`op_true`/`op_false` already
   let literal Int/BV/Bool constants be recognized. *)
let op_seq_unit : decl_kind = Z3OperatorTags.op_seq_unit

(* Binary Boolean connectives `and`/`or`/`=>`, added so the QF_UF
   benchmark corpus's dominant unmatched `Rewrite` shapes -- Z3's own
   Tseitin/NNF-style De Morgan (`(and a b) = (not (or (not a) (not
   b)))`) and implication-elimination (`(a => b) = (or (not a) b)`)
   normalizations -- can be recognized as genuine tautologies (see
   `Z3PatternMatchedProofChecker.fst`'s `demorgan_and_leaf_ok`/
   `implies_as_or_leaf_ok`). Z3's real `and`/`or` are n-ary; only the
   binary (arity-2) instance is modeled here, matching every `and`/`or`
   application actually observed in the sampled proofs this was added
   for -- `decl_shape_ok` rejects any other arity, so a wider `and`/`or`
   application simply stays uninterpreted (`None`), same as any other
   not-yet-modeled op. *)
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
