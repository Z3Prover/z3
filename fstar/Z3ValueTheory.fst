(*
   Z3ValueTheory.fst

   The shared semantic value domain, and the interpreted-operator
   vocabulary (`decl_kind` codes), that every per-theory interpretation
   module (`Z3ArrayInterp.fst`, `Z3SeqInterp.fst`, `Z3BvInterp.fst`)
   and `Z3InterpretedProofChecker.fst`'s own "core" (bool/arith/`eq`)
   ops are built against.

   This type/these constants used to live directly inside
   `Z3InterpretedProofChecker.fst`. They were pulled out into their own
   module so that each theory's `arr`/`seq`/`bv` value representation
   (`Z3ArrayTheory.fst`/`Z3SeqTheory.fst`/`Z3BvTheory.fst`) can be
   wrapped by a small, *theory-owned* `interp_app : decl_kind -> list
   value -> option value` dispatcher -- `Z3ArrayTheory.fst` itself
   stays untouched (pure `arr`/`select`/`store` plus lemmas, with no
   notion of `value` or `decl_kind` at all), while `Z3ArrayInterp.fst`
   is the thin, `value`-aware companion module that *does* need both
   `Z3ArrayTheory.fst` (for `arr`/`select`/`store`) and this module
   (for `value`/`op_select`/`op_store`). Had `value` instead been
   defined *inside* one of the theory files (or `value` left inside
   `Z3InterpretedProofChecker.fst`, with each theory file in turn
   trying to depend on it for its own `interp_app`), the two files
   would need each other and F* has no notion of mutually-recursive
   modules -- hence this separate, dependency-free-of-any-theory's-
   `interp_app` home for `value` itself.
*)
module Z3ValueTheory
open Z3AstTheory

(* ----------------------------------------------------------------- *)
(* A concrete semantic domain covering every theory exercised here:    *)
(* Int/Bool (arith/bool), an array from Int to Int                     *)
(* (`Z3ArrayTheory.arr int int`, matching SMT-LIB's `(Array Int Int)`), *)
(* a sequence of Int (`Z3SeqTheory.seq int`, matching `(Seq Int)`), and *)
(* a 32-bit bitvector (`Z3BvTheory.bv 32`). Kept at `int`/`int`         *)
(* element/index types rather than the fully generic `value` itself,   *)
(* deliberately: embedding `value` as an array/sequence *element* type  *)
(* would make `value` need to be an `eqtype` (`Z3SeqTheory.seq`         *)
(* requires `a:eqtype`), which a function-typed constructor (`VArr`)    *)
(* can never satisfy (no decidable equality on functions) -- so this    *)
(* domain is deliberately first-order/non-recursive, matching exactly   *)
(* the sorts the example leaves below actually use.                     *)
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
let op_not : decl_kind = 1
let op_plus : decl_kind = 2
let op_select : decl_kind = 3
let op_store : decl_kind = 4
let op_bvand : decl_kind = 5
let op_concat : decl_kind = 6
(* Polymorphic equality (any sort `s`, `domain = [s;s]`, `range = Bool`).
   Added together with the injective-naming fix below so an `eq_symm`
   rewrite matcher can be proved sound without any new model axioms. *)
let op_eq : decl_kind = 7

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
let op_true : decl_kind = 8
let op_false : decl_kind = 9
let op_num_int : decl_kind = 10
let op_num_bv : decl_kind = 11

(* `seq.unit`: wraps a single `Int` element into the length-1
   sequence containing it (`Z3SeqTheory.unit`). Added so that
   `is_unique_value` (`Z3PatternMatchedProofChecker.fst`) can
   recognize sequence *literals* -- i.e. values built purely from
   `seq.unit`/`op_concat` applied to unique-value elements, with no
   uninterpreted sub-term anywhere -- as themselves unique values,
   mirroring how `op_num_int`/`op_num_bv`/`op_true`/`op_false` already
   let literal Int/BV/Bool constants be recognized. *)
let op_seq_unit : decl_kind = 12

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
let op_and : decl_kind = 13
let op_or : decl_kind = 14
let op_implies : decl_kind = 15

(* Proof-only observational equivalence, not an executable Boolean op. *)
let op_oeq : decl_kind = 16

let op_mul : decl_kind = 17
let op_array_ext : decl_kind = 18
