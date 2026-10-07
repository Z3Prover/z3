(*
   Z3BasicExprTheory.fst

   Recognizers and a denotational evaluator for the `basic_family_id`
   expression constructs (src/ast/ast.h, `enum basic_op_kind`): the
   propositional connectives (`and`/`or`/`not`/`implies`/`xor`),
   equality/distinctness (`=`/`distinct`), truth constants
   (`true`/`false`), and if-then-else (`ite`) -- built on top of
   Z3AstTheory.fst's generic `expr`/`interpretation` machinery exactly
   as Z3RegexExprTheory.fst connects that same machinery to regular
   expressions. The proof-object constructs that share
   `basic_op_kind`'s numbering space (`PR_*`, `OP_OEQ`) are not
   expression-level nodes Z3 regex/sequence reasoning ever needs, so
   they are intentionally omitted.

   `basic_op_kind`'s declaration order (`OP_TRUE` = 0, ..., `OP_OEQ` =
   10) is mirrored exactly by `decl_kind_of` below, the same
   convention `Z3RegexExprTheory.fst`'s `decl_kind_of` uses for
   `seq_op_kind` (there starting at 15); the two ranges do not
   overlap, so a single shared `Z3AstTheory.decl_kind` ( = `int`)
   space can encode "the interpreted symbol this `func_decl` denotes"
   for both families simultaneously (a `func_decl.interp` value is
   only ever compared against one specific family's `decl_kind_of` at
   a time, exactly as real Z3 additionally keys symbols by
   `family_id`, which this simplified model elides since the two
   integer ranges used here happen never to collide).

   This file's primary purpose is to let `Z3RegexExprTheory.fst`'s
   `to_lang` and `Z3RegexInfo.fst`'s `compute_info` handle `(ite c t
   f)` where `t`/`f` are regex-sorted (`seq_decl_plugin.cpp`'s
   `mk_info_rec`'s `u.m.is_ite(e, c, t, f)` fallback case, answered
   with `info::orelse`): `eval_bool` gives a closed Boolean-sorted
   condition expression `c` a concrete truth value, so that `to_lang`
   can pick the actual (model-dependent) branch while `compute_info`
   -- mirroring the real static analysis, which cannot know which
   branch will be taken -- combines both branches' `info` with
   `info_orelse` regardless.
*)
module Z3BasicExprTheory

open Z3AstTheory
module Classical = FStar.Classical

(* ----------------------------------------------------------------- *)
(* `basic_op_kind` (src/ast/ast.h), expression-level subset            *)
(* ----------------------------------------------------------------- *)

type basic_op =
  | Op_true     (* OP_TRUE,     index 0 *)
  | Op_false    (* OP_FALSE,    index 1 *)
  | Op_eq       (* OP_EQ,       index 2 *)
  | Op_distinct (* OP_DISTINCT, index 3 *)
  | Op_ite      (* OP_ITE,      index 4 *)
  | Op_and      (* OP_AND,      index 5 *)
  | Op_or       (* OP_OR,       index 6 *)
  | Op_xor      (* OP_XOR,      index 7 *)
  | Op_not      (* OP_NOT,      index 8 *)
  | Op_implies  (* OP_IMPLIES,  index 9 *)

let decl_kind_of (op:basic_op) : decl_kind =
  match op with
  | Op_true     -> 0
  | Op_false    -> 1
  | Op_eq       -> 2
  | Op_distinct -> 3
  | Op_ite      -> 4
  | Op_and      -> 5
  | Op_or       -> 6
  | Op_xor      -> 7
  | Op_not      -> 8
  | Op_implies  -> 9

(* `decl_kind_of` is injective: distinct `basic_op`s never collide
   (checked once and for all, as `Z3RegexExprTheory.fst` does for
   `re_op`). *)
let lemma_decl_kind_of_injective (op1 op2:basic_op)
  : Lemma (requires decl_kind_of op1 = decl_kind_of op2) (ensures op1 == op2)
  = ()

(* `f` is (the declaration of) an application of `op`. *)
let is_basic_op (f:func_decl) (op:basic_op) : bool =
  match f.interp with
  | Some k -> k = decl_kind_of op
  | None -> false

(* ----------------------------------------------------------------- *)
(* Equality/distinctness helpers                                       *)
(* ----------------------------------------------------------------- *)

let rec all_distinct_from (#value:eqtype) (x:value) (rest:list value) : bool =
  match rest with
  | [] -> true
  | y :: rest' -> x <> y && all_distinct_from x rest'

(* `(distinct a1 ... an)`: every pair of arguments denotes a different
   value, mirroring Z3's n-ary `OP_DISTINCT`. *)
let rec all_distinct (#value:eqtype) (vs:list value) : bool =
  match vs with
  | [] -> true
  | x :: rest -> all_distinct_from x rest && all_distinct rest

(* ----------------------------------------------------------------- *)
(* Boolean evaluation                                                   *)
(* ----------------------------------------------------------------- *)

(* `eval_bool i to_bool e rho` gives a Bool-sorted `e` a concrete
   truth value: the propositional connectives and `ite` recurse
   structurally; `=`/`distinct` compare the generic `value`
   denotations of their (possibly non-Boolean-sorted) arguments via
   `Z3AstTheory.eval`, hence requiring `value:eqtype`; any other node
   (an uninterpreted Boolean atom, or an application from a different
   family entirely, e.g. a string/arithmetic predicate this theory
   does not recognize) falls back to `to_bool` applied to its generic
   `eval`uation -- the one place genuine model-dependence enters for
   atoms this module does not itself interpret. `and`/`or` are
   modeled as Z3 actually represents them, n-ary (not fixed arity 2),
   via the sibling `eval_and`/`eval_or`. *)
let rec eval_bool (#value:eqtype) (i:interpretation value) (to_bool:value -> bool) (e:expr) (rho:env value)
  : Tot bool (decreases e)
  = match e with
    | Var _ _ -> to_bool (eval i e rho)
    | Quantifier _ _ _ -> to_bool (eval i e rho)
    | App f args ->
      if is_basic_op f Op_true then true
      else if is_basic_op f Op_false then false
      else if is_basic_op f Op_not then
        (match args with
         | [a] -> not (eval_bool i to_bool a rho)
         | _ -> to_bool (eval i e rho))
      else if is_basic_op f Op_and then eval_and i to_bool args rho
      else if is_basic_op f Op_or then eval_or i to_bool args rho
      else if is_basic_op f Op_implies then
        (match args with
         | [a; b] -> (not (eval_bool i to_bool a rho)) || eval_bool i to_bool b rho
         | _ -> to_bool (eval i e rho))
      else if is_basic_op f Op_xor then
        (match args with
         | [a; b] -> eval_bool i to_bool a rho <> eval_bool i to_bool b rho
         | _ -> to_bool (eval i e rho))
      else if is_basic_op f Op_eq then
        (match args with
         | [a; b] -> eval i a rho = eval i b rho
         | _ -> to_bool (eval i e rho))
      else if is_basic_op f Op_distinct then all_distinct (eval_args i args rho)
      else if is_basic_op f Op_ite then
        (match args with
         | [c; t; fe] -> if eval_bool i to_bool c rho then eval_bool i to_bool t rho else eval_bool i to_bool fe rho
         | _ -> to_bool (eval i e rho))
      else to_bool (eval i e rho)

and eval_and (#value:eqtype) (i:interpretation value) (to_bool:value -> bool) (args:list expr) (rho:env value)
  : Tot bool (decreases args)
  = match args with
    | [] -> true
    | a :: rest -> eval_bool i to_bool a rho && eval_and i to_bool rest rho

and eval_or (#value:eqtype) (i:interpretation value) (to_bool:value -> bool) (args:list expr) (rho:env value)
  : Tot bool (decreases args)
  = match args with
    | [] -> false
    | a :: rest -> eval_bool i to_bool a rho || eval_or i to_bool rest rho

(* ----------------------------------------------------------------- *)
(* Basic facts                                                         *)
(* ----------------------------------------------------------------- *)

(* `not (not a)` agrees with `a` -- a direct sanity check that
   `eval_bool`'s `Op_not` case really is Boolean negation. *)
let lemma_eval_bool_double_negation (#value:eqtype) (i:interpretation value) (to_bool:value -> bool)
    (f_not:func_decl{is_basic_op f_not Op_not}) (a:expr) (rho:env value)
  : Lemma (eval_bool i to_bool (App f_not [App f_not [a]]) rho == eval_bool i to_bool a rho)
  = ()

(* `distinct` really does demand pairwise difference: two arguments
   that are `distinct` cannot have equal `eval`uations. *)
let lemma_eval_bool_distinct_pairwise (#value:eqtype) (i:interpretation value) (to_bool:value -> bool)
    (f_di:func_decl{is_basic_op f_di Op_distinct}) (a b:expr) (rho:env value)
  : Lemma (requires eval_bool i to_bool (App f_di [a; b]) rho)
          (ensures eval i a rho <> eval i b rho)
  = ()
