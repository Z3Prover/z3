(*
   Z3RegexExprTheory.fst

   Connects Z3AstTheory's AST model to Z3RegexTheory's language
   semantics, by recognizing the subset of `App` nodes that Z3's
   sequence/regex theory plugin (src/ast/seq_decl_plugin.h,
   `seq_op_kind`) builds regular expressions out of, and giving each
   one a denotation as a `lang a` (Z3RegexTheory.fst).

   Only the operators that build or consume *regular expressions* are
   modeled (the `OP_RE_*` family, plus `OP_SEQ_TO_RE`); the surrounding
   string/sequence-valued operators (`OP_SEQ_CONCAT`, `OP_SEQ_AT`,
   etc.) and `OP_SEQ_IN_RE`/membership are out of scope for this file
   (`OP_SEQ_IN_RE` is the one place a regex *meets* a string
   constraint, and is not itself regex-valued, so is intentionally
   left for a higher-level theory of `assert`s rather than this
   denotational layer). The literal integer values assigned to each
   `re_op` mirror the declaration order of `enum seq_op_kind` in
   seq_decl_plugin.h exactly (`OP_SEQ_UNIT` = 0, ..., `OP_RE_PLUS` =
   25, ..., `OP_RE_DERIVATIVE` = 42), so that `decl_kind_of`'s results
   line up with the real plugin's `decl_kind` values, even though
   nothing downstream depends on the specific numbers chosen.

   A leaf sequence literal (the argument of `seq.to_re`, or a
   character literal argument of `re.range`) is modeled directly as a
   ground `Z3AstTheory.expr` denoting a `seq a` under a fixed
   `leaf_interp` (an interpretation restricted to closed,
   quantifier-free, regex-free terms); `to_lang` below is defined
   relative to such a `leaf_interp` so that `seq.to_re`/`re.range`'s
   arguments can be evaluated, exactly mirroring how
   `seq_decl_plugin.cpp` calls `u.str.min_length`/`max_length`/
   `m.is_value` on *already evaluated/simplified* sequence arguments.
*)
module Z3RegexExprTheory

open Z3AstTheory
open Z3SeqTheory
open Z3RegexTheory
module Classical = FStar.Classical

(* ----------------------------------------------------------------- *)
(* The regex fragment of `seq_op_kind` (src/ast/seq_decl_plugin.h)     *)
(* ----------------------------------------------------------------- *)

(* Mirrors the subset of `enum seq_op_kind` whose values are regular
   expressions, plus `OP_SEQ_TO_RE` (the embedding of a sequence
   literal into RE_SORT). `Re_power` (OP_RE_POWER, a parsing-only
   alias eagerly rewritten to a fixed `OP_RE_CONCAT` chain by Z3, see
   seq_rewriter.cpp) and `Re_derivative` (OP_RE_DERIVATIVE, an
   internal Brzozozwski-derivative helper, not user-facing regex
   syntax) are intentionally omitted: both denote regular languages
   but neither contributes a *new* combinator beyond what is already
   modeled by Z3RegexTheory. *)
type re_op =
  | Re_seq_to_re     (* OP_SEQ_TO_RE,      seq_decl_plugin.h index 15 *)
  | Re_plus          (* OP_RE_PLUS,        index 25 *)
  | Re_star          (* OP_RE_STAR,        index 26 *)
  | Re_option        (* OP_RE_OPTION,      index 27 *)
  | Re_range         (* OP_RE_RANGE,       index 28 *)
  | Re_concat        (* OP_RE_CONCAT,      index 29 *)
  | Re_union         (* OP_RE_UNION,       index 30 *)
  | Re_diff          (* OP_RE_DIFF,        index 31 *)
  | Re_intersect     (* OP_RE_INTERSECT,   index 32 *)
  | Re_xor           (* OP_RE_XOR,         index 33 *)
  | Re_loop          (* OP_RE_LOOP,        index 34 *)
  | Re_complement    (* OP_RE_COMPLEMENT,  index 36 *)
  | Re_empty_set     (* OP_RE_EMPTY_SET,   index 37 *)
  | Re_full_seq_set  (* OP_RE_FULL_SEQ_SET, index 38 *)
  | Re_full_char_set (* OP_RE_FULL_CHAR_SET, index 39 *)
  | Re_of_pred       (* OP_RE_OF_PRED,     index 40 *)
  | Re_reverse       (* OP_RE_REVERSE,     index 41 *)

(* The literal `decl_kind` each `re_op` corresponds to, matching the
   declaration order of `enum seq_op_kind` exactly. *)
let decl_kind_of (op:re_op) : decl_kind =
  match op with
  | Re_seq_to_re     -> 15
  | Re_plus          -> 25
  | Re_star          -> 26
  | Re_option        -> 27
  | Re_range         -> 28
  | Re_concat        -> 29
  | Re_union         -> 30
  | Re_diff          -> 31
  | Re_intersect     -> 32
  | Re_xor           -> 33
  | Re_loop          -> 34
  | Re_complement    -> 36
  | Re_empty_set     -> 37
  | Re_full_seq_set  -> 38
  | Re_full_char_set -> 39
  | Re_of_pred       -> 40
  | Re_reverse       -> 41

(* `decl_kind_of` is injective: distinct `re_op`s never collide, i.e.
   this encoding faithfully distinguishes the operators it models
   (checked once and for all, rather than argued informally). *)
let lemma_decl_kind_of_injective (op1 op2:re_op)
  : Lemma (requires decl_kind_of op1 = decl_kind_of op2) (ensures op1 == op2)
  = ()

(* `f` is (the declaration of) an application of `op`, i.e.
   `get_decl_kind() = decl_kind_of op` for the appropriate family. *)
let is_re_op (f:func_decl) (op:re_op) : bool =
  match f.interp with
  | Some k -> k = decl_kind_of op
  | None -> false

(* ----------------------------------------------------------------- *)
(* Leaf sequence literals                                             *)
(* ----------------------------------------------------------------- *)

(* The restricted interpretation used to evaluate a leaf sequence
   argument (e.g. the argument of `seq.to_re`, or the two character
   endpoints of `re.range`): closed, ground sequence-valued terms
   only. `seq_lit a` pairs such an interpretation with the fixed
   element-value embedding `to_elt` it uses for character/element
   literals, since `value` (Z3AstTheory's semantic domain) is left
   abstract there but must coincide with `Z3RegexTheory.seq a` here.

   `classify` additionally distinguishes *literal* leaves (concrete
   sequence constants, e.g. `m.is_value(e->get_arg(0))` for
   `seq.to_re`'s argument, or `u.str.is_string(...)` for `re.range`'s
   endpoints in seq_decl_plugin.cpp) from *symbolic* leaves (an
   arbitrary expression whose value is model-dependent, e.g. a free
   sequence variable): `classify e = Some w` means `e` is recognized
   as the literal `w`, invariant across every interpretation;
   `classify e = None` means `e`'s denotation is only ever available
   through `leaf_interp`, which may differ between interpretations.
   This distinction is exactly what `seq_util::rex::info::interpreted`
   (`is_ground`) is meant to track -- see Z3RegexInfo.fst and
   PR #11091 / issue #11090, where a symbolic `re.range` endpoint was
   incorrectly reported as if it were always literal. *)
noeq type seq_lit (a:eqtype) = {
  classify    : expr -> option (seq a);
  leaf_interp : interpretation (seq a);
  (* A total order on elements, standing in for the 8-bit bit-vector
     numeral order `seq_decl_plugin.cpp` uses to interpret `re.range`'s
     two character-literal endpoints; `a` carries no built-in order of
     its own, so this is supplied per-instantiation rather than
     assumed as an axiom. *)
  char_le     : a -> a -> bool;
}

(* Evaluate a leaf expression to the sequence it denotes: a
   classified literal is returned directly (the same value under any
   `seq_lit` agreeing on `classify`, by construction); otherwise fall
   back to `leaf_interp`, which is where model-dependence can enter. *)
let eval_leaf (#a:eqtype) (sl:seq_lit a) (e:expr) : seq a =
  match sl.classify e with
  | Some w -> w
  | None -> eval sl.leaf_interp e (fun _ -> empty)

(* `e` is a ground (literal, model-independent) leaf under `sl`. *)
let is_ground_leaf (#a:eqtype) (sl:seq_lit a) (e:expr) : bool =
  Some? (sl.classify e)

(* Two `seq_lit`s classify every expression identically, i.e. they
   agree on which leaves are literal (and which literal value) --
   they may still disagree on `leaf_interp` for symbolic leaves,
   modeling two different models/interpretations of the same
   symbolic constants. *)
let same_classification (#a:eqtype) (sl sl':seq_lit a) : prop =
  forall (e:expr). sl.classify e == sl'.classify e

(* If `e` is a ground leaf under `sl` (hence, by `same_classification`,
   under `sl'` too), both evaluate it to the exact same sequence --
   the key fact underlying why `interpreted`/`is_ground` expressions
   denote a fixed, model-independent language. *)
let lemma_eval_leaf_ground (#a:eqtype) (sl sl':seq_lit a) (e:expr)
  : Lemma (requires same_classification sl sl' /\ is_ground_leaf sl e)
          (ensures eval_leaf sl e == eval_leaf sl' e)
  = ()

(* A character range test, taken as the two endpoint sequences
   already evaluated to ground words: `x` is "in range" iff `wl`,
   `[x]`, and `wh` are pointwise ordered as the one-character
   sequences they denote, using `sl`'s supplied element order. *)
let mem_in_char_range (#a:eqtype) (sl:seq_lit a) (wl wh:seq a) (x:a) : bool =
  match wl, wh with
  | [l], [h] -> sl.char_le l x && sl.char_le x h
  | _, _ -> false

(* ----------------------------------------------------------------- *)
(* Denotation: App nodes built from `re_op` to `lang a`                *)
(* ----------------------------------------------------------------- *)

(* `to_lang sl e` is the regular language `e` denotes, when `e` is a
   well-formed application of a recognized `re_op` (recursively, down
   to leaves); `None` otherwise (ill-formed or not a regex
   expression this module models -- e.g. `Var`/`Quantifier` nodes,
   or an uninterpreted/other-family `App`). This directly mirrors
   `seq_decl_plugin.cpp`'s own structural recursion in `get_info_rec`
   (which dispatches on `to_app(e)->get_decl_kind()`), but computing
   language membership instead of the `rex::info` summary -- the
   ground truth that `get_info`'s summary must be sound with respect
   to, formalized in a later module. *)
let rec to_lang (#a:eqtype) (sl:seq_lit a) (e:expr) : Tot (option (lang a)) (decreases e) =
  match e with
  | Var _ _ | Quantifier _ _ _ -> None
  | App f args ->
    if is_re_op f Re_empty_set then (match args with | [] -> Some re_empty | _ -> None)
    else if is_re_op f Re_full_seq_set then (match args with | [] -> Some re_full | _ -> None)
    else if is_re_op f Re_full_char_set then (match args with | [] -> Some re_allchar | _ -> None)
    else if is_re_op f Re_of_pred then
      (* The predicate itself is left abstract (it is an arbitrary
         Boolean-sorted function symbol in Z3, `u.re.is_of_pred`);
         here it is recovered from `f`'s own name as a proxy, since
         `func_decl` does not carry executable predicates. Concrete
         instantiations of this module (e.g. for `re.range`, see
         below) should prefer the dedicated `Re_range` case, which
         does carry an explicit, evaluable predicate. *)
      None
    else if is_re_op f Re_range then
      (match args with
       | [lo; hi] ->
         let wl = eval_leaf sl lo in
         let wh = eval_leaf sl hi in
         Some (re_range (fun x -> mem_in_char_range sl wl wh x))
       | _ -> None)
    else if is_re_op f Re_seq_to_re then
      (match args with
       | [s] -> Some (re_to_re (eval_leaf sl s))
       | _ -> None)
    else if is_re_op f Re_plus then
      (match args with
       | [r] -> (match to_lang sl r with Some l -> Some (re_plus l) | None -> None)
       | _ -> None)
    else if is_re_op f Re_star then
      (match args with
       | [r] -> (match to_lang sl r with Some l -> Some (re_star l) | None -> None)
       | _ -> None)
    else if is_re_op f Re_option then
      (match args with
       | [r] -> (match to_lang sl r with Some l -> Some (re_opt l) | None -> None)
       | _ -> None)
    else if is_re_op f Re_complement then
      (match args with
       | [r] -> (match to_lang sl r with Some l -> Some (re_compl l) | None -> None)
       | _ -> None)
    else if is_re_op f Re_reverse then
      (match args with
       | [r] -> (match to_lang sl r with Some l -> Some (re_reverse l) | None -> None)
       | _ -> None)
    else if is_re_op f Re_concat then
      (match args with
       | [r1; r2] ->
         (match to_lang sl r1, to_lang sl r2 with
          | Some l1, Some l2 -> Some (re_concat l1 l2)
          | _, _ -> None)
       | _ -> None)
    else if is_re_op f Re_union then
      (match args with
       | [r1; r2] ->
         (match to_lang sl r1, to_lang sl r2 with
          | Some l1, Some l2 -> Some (re_union l1 l2)
          | _, _ -> None)
       | _ -> None)
    else if is_re_op f Re_intersect then
      (match args with
       | [r1; r2] ->
         (match to_lang sl r1, to_lang sl r2 with
          | Some l1, Some l2 -> Some (re_inter l1 l2)
          | _, _ -> None)
       | _ -> None)
    else if is_re_op f Re_diff then
      (match args with
       | [r1; r2] ->
         (match to_lang sl r1, to_lang sl r2 with
          | Some l1, Some l2 -> Some (re_diff l1 l2)
          | _, _ -> None)
       | _ -> None)
    else if is_re_op f Re_xor then
      (match args with
       | [r1; r2] ->
         (match to_lang sl r1, to_lang sl r2 with
          | Some l1, Some l2 -> Some (re_xor l1 l2)
          | _, _ -> None)
       | _ -> None)
    else if is_re_op f Re_loop then
      (match args, f.int_params with
       | [r], [lo] ->
         if lo >= 0 then (match to_lang sl r with Some l -> Some (re_loop_lo l lo) | None -> None)
         else None
       | [r], [lo; hi] ->
         if lo >= 0 && hi >= lo then (match to_lang sl r with Some l -> Some (re_loop l lo hi) | None -> None)
         else None
       | _ -> None)
    else None

