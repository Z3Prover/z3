(*
   Z3AstTheory.fst

   A self-contained, deliberately simplified axiomatization, in F*, of
   the shape of Z3's expression DAG, as defined by src/ast/ast.h. This
   module is a structural model of ASTs only: it fixes the five kinds
   of node that Z3's `ast` class distinguishes and the fields each one
   carries, together with a well-formedness (well-sortedness) judgment
   and a denotational semantics parameterized by an interpretation of
   uninterpreted symbols. It intentionally does not attempt to model
   the full generality of Z3's `ast_manager` (hash-consing, reference
   counting, families/plugins beyond what is needed downstream, proof
   objects, etc.) -- only as much structure as is needed so that later
   modules (`Z3RegexExprTheory.fst`, the `get_info` formalization) can
   talk about "the Expr that denotes this regex" and "the language it
   denotes" precisely.

   Correspondence with src/ast/ast.h:

     ast_kind      ~  five node kinds: AST_APP, AST_VAR, AST_QUANTIFIER,
                      AST_SORT, AST_FUNC_DECL. This module models the
                      three *expression* kinds (AST_APP, AST_VAR,
                      AST_QUANTIFIER) as the inductive type `expr`, and
                      AST_SORT/AST_FUNC_DECL as the separate types
                      `sort`/`func_decl` that expressions are built
                      from, matching that `sort`/`func_decl` are
                      themselves `ast` nodes in Z3 but are not among
                      the three expression kinds (`is_app`/`is_var`/
                      `is_quantifier` are mutually exclusive and
                      disjoint from `is_sort`/`is_func_decl`).

     sort          ~  `class sort : public decl`: here reduced to a
                      symbolic sort identifier (name); a
                      family_id/parameter list is not modeled, since
                      downstream only the regex/sequence sort matters.

     func_decl     ~  `class func_decl : public decl`: carries a name,
                      a domain (list of argument sorts), a range sort,
                      and -- for interpreted symbols -- a
                      `(family_id, decl_kind)` pair (mirroring
                      `get_family_id()`/`get_decl_kind()`); `None` for
                      the family/kind pair models an uninterpreted
                      declaration (`null_family_id`, see
                      `is_uninterp`).

     var           ~  `class var : public expr`: a de Bruijn index
                      (`m_idx`) and a sort.

     app           ~  `class app : public expr`: a `func_decl` applied
                      to a list of argument expressions
                      (`get_decl()`/`get_args()`/`get_num_args()`).

     quantifier     ~  `class quantifier : public expr`: a
                      `quantifier_kind` (`forall_k`/`exists_k`/
                      `lambda_k`), the sorts of the bound variables,
                      and a body expression.

   Well-sortedness (`wf`) mirrors the invariant Z3's `ast_manager`
   maintains by construction (every `app`'s arguments match its
   `func_decl`'s domain, bound variable indices are in range, etc.);
   it is needed so that the semantics below is total only where it
   should be.
*)
module Z3AstTheory

(* ----------------------------------------------------------------- *)
(* Sorts                                                               *)
(* ----------------------------------------------------------------- *)

(* A sort is modeled abstractly by its name; `sort_eq` stands in for
   Z3's hash-consing-based pointer equality on `sort*`. *)
type sort = { sort_name : string }

let sort_eq (s1 s2:sort) : bool = s1.sort_name = s2.sort_name

(* ----------------------------------------------------------------- *)
(* Function declarations                                              *)
(* ----------------------------------------------------------------- *)

(* An interpreted symbol's identity, i.e. `(get_family_id(),
   get_decl_kind())`; left abstract (any eqtype) since downstream
   modules instantiate it with the specific `OP_RE_*`/`OP_SEQ_*`
   constants from src/ast/seq_decl_plugin.h. *)
type decl_kind = int

type func_decl = {
  decl_name   : string;
  domain      : list sort;
  range       : sort;
  (* `Some k`  ~ an interpreted declaration with decl_kind k, i.e.
                 get_family_id() <> null_family_id (see is_uninterp);
     `None`    ~ an uninterpreted constant/function symbol. *)
  interp      : option decl_kind;
  (* ~ `class parameter`'s `PARAM_INT` case: the integer parameters
     decorating a declaration, e.g. `re.loop`'s lower/upper bounds,
     which Z3 attaches to the `func_decl` itself rather than passing
     as ordinary `expr` arguments (`parameter::PARAM_INT`, see
     ast.h). Only integer parameters are modeled, since that is all
     downstream (`OP_RE_LOOP`) needs. *)
  int_params  : list int;
}

let is_uninterp_decl (f:func_decl) : bool = None? f.interp

(* ----------------------------------------------------------------- *)
(* Quantifier kind                                                     *)
(* ----------------------------------------------------------------- *)

type quantifier_kind =
  | Forall_k
  | Exists_k
  | Lambda_k

(* ----------------------------------------------------------------- *)
(* Expressions: the three expression kinds of `ast_kind`               *)
(* ----------------------------------------------------------------- *)

(* AST_VAR, AST_APP, AST_QUANTIFIER. A de Bruijn representation is
   used for bound variables, exactly as Z3's `var` class does
   (`m_idx`), so `Quantifier` need not carry substitution machinery of
   its own: `Var i` inside a quantifier's body refers to the i-th
   enclosing binder (0 = innermost), as in `src/ast/ast.h`'s
   `var(unsigned idx, sort * s)`. *)
type expr =
  | Var        : idx:nat -> s:sort -> expr
  | App        : decl:func_decl -> args:list expr -> expr
  | Quantifier : qk:quantifier_kind -> bound_sorts:list sort -> body:expr -> expr

(* ----------------------------------------------------------------- *)
(* Sort of an expression (mirrors `expr::get_sort()`)                  *)
(* ----------------------------------------------------------------- *)

(* Quantifiers (forall/exists) are always Bool-sorted; a lambda's sort
   would be an array sort built from `bound_sorts` and the body's
   sort, which is not needed downstream, so `lambda_sort` stands in
   for it uninterpreted. *)
let bool_sort : sort = { sort_name = "Bool" }
let lambda_sort : sort = { sort_name = "Lambda" }

let get_sort (e:expr) : sort =
  match e with
  | Var _ s -> s
  | App f _ -> f.range
  | Quantifier qk _ _ ->
    (match qk with
     | Forall_k | Exists_k -> bool_sort
     | Lambda_k -> lambda_sort)

(* ----------------------------------------------------------------- *)
(* Well-sortedness                                                     *)
(* ----------------------------------------------------------------- *)

(* Pointwise sort-matching of an argument list against a domain, as
   `app`'s constructor enforces when built via `ast_manager::mk_app`. *)
let rec sorts_match (args:list expr) (dom:list sort) : bool =
  match args, dom with
  | [], [] -> true
  | a :: args', d :: dom' -> sort_eq (get_sort a) d && sorts_match args' dom'
  | _, _ -> false

(* `wf n e` holds iff every `App` node in `e` has arguments matching
   its declaration's domain, and every `Var` is well-sorted at its
   binding depth, where `n` counts the quantifier nestings enclosing
   `e` (so top-level calls use `wf 0 e`, i.e. `e` is a closed term
   with no dangling bound variables). This does not bound `idx` by
   `n`, matching that Z3 permits (but `ast_manager` never
   constructs) free variables in a standalone `expr*`; well-formed
   *closed* expressions are additionally required to have no `Var`
   nodes at all, via `closed` below. *)
let rec wf (e:expr) : bool =
  match e with
  | Var _ _ -> true
  | App f args -> sorts_match args f.domain && wf_args args
  | Quantifier _ _ body -> wf body

and wf_args (args:list expr) : bool =
  match args with
  | [] -> true
  | a :: args' -> wf a && wf_args args'

(* `closed e` holds iff `e` contains no out-of-range bound variable,
   i.e. every `Var idx _` inside is bound by an enclosing `Quantifier`
   (idx < number of quantifiers strictly enclosing it, counting from
   the innermost). This is the F* counterpart of the invariant that a
   top-level `expr*` returned by `ast_manager` never has a dangling de
   Bruijn index. *)
let rec closed_at (depth:nat) (e:expr) : Tot bool (decreases e) =
  match e with
  | Var idx _ -> idx < depth
  | App _ args -> closed_at_args depth args
  | Quantifier _ bound_sorts body -> closed_at (depth + List.Tot.length bound_sorts) body
and closed_at_args (depth:nat) (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: args' -> closed_at depth a && closed_at_args depth args'

let closed (e:expr) : bool = closed_at 0 e

(* ----------------------------------------------------------------- *)
(* Semantics                                                           *)
(* ----------------------------------------------------------------- *)

(* A `value` is left abstract: downstream modules (e.g.
   Z3RegexExprTheory) instantiate it with Z3SeqTheory's `seq a` for
   sequence/regex-sorted expressions; other sorts are out of scope
   here. An interpretation provides: (1) meaning for every
   interpreted `func_decl` (`interp_app`), applied to already-denoted
   arguments, and (2) meaning for every uninterpreted constant/
   function symbol under some fixed valuation (`uninterp_app`),
   mirroring how a `model` assigns interpretations to uninterpreted
   symbols. Bound variables are evaluated against an explicit
   environment (`env`), a list of values indexed exactly as `Var`'s de
   Bruijn index, innermost-first -- the semantic analogue of
   substituting a quantifier's bound variables. *)
noeq type interpretation (value:Type) = {
  interp_app    : f:func_decl{Some? f.interp} -> list value -> value;
  uninterp_app  : f:func_decl{is_uninterp_decl f} -> list value -> value;
  (* Denotation of a quantifier node, given the (already-shifted)
     denotation of its body as a function of one bound-variable
     assignment per `bound_sorts` entry. Left abstract: this module
     does not commit to a particular treatment of quantification
     (e.g. Boolean-valued forall/exists over a domain of values, or
     lambda-as-function), since none of it is needed by the
     regex/sequence track that motivates this file. *)
  interp_quant  : quantifier_kind -> bound_sorts:list sort -> body_sem:(list value -> value) -> value;
}

(* `env` is a de Bruijn environment: `env i` is the value bound to
   `Var i _`, with index 0 the innermost (most recently opened)
   binder, as in `src/ast/ast.h`'s `var` semantics under
   substitution. *)
type env (value:Type) = nat -> value

let shift (#value:Type) (vs:list value) (e:env value) : env value =
  fun i ->
    if i < List.Tot.length vs then List.Tot.index vs i
    else e (i - List.Tot.length vs)

(* `eval e env` denotes `e` under the given variable environment and
   interpretation; only defined (total) on well-sorted expressions,
   matching that only well-formed `expr*` nodes are ever produced by
   `ast_manager`. *)
let rec eval (#value:Type) (i:interpretation value) (e:expr) (rho:env value) : value =
  match e with
  | Var idx _ -> rho idx
  | App f args ->
    let vs = eval_args i args rho in
    if Some? f.interp then i.interp_app f vs else i.uninterp_app f vs
  | Quantifier qk bound_sorts body ->
    i.interp_quant qk bound_sorts (fun vs -> eval i body (shift vs rho))

and eval_args (#value:Type) (i:interpretation value) (args:list expr) (rho:env value) : list value =
  match args with
  | [] -> []
  | a :: args' -> eval i a rho :: eval_args i args' rho

(* ----------------------------------------------------------------- *)
(* Basic structural facts                                              *)
(* ----------------------------------------------------------------- *)

(* The three expression kinds are mutually exclusive, matching that
   `is_app`/`is_var`/`is_quantifier` partition `AST_APP`/`AST_VAR`/
   `AST_QUANTIFIER` (a direct consequence of `expr` being an
   inductive type with distinct constructors, stated here for
   documentation parity with ast.h's helper predicates). *)
let lemma_expr_kinds_disjoint (e:expr)
  : Lemma ((Var? e <==> ~(App? e \/ Quantifier? e)) /\
           (App? e <==> ~(Var? e \/ Quantifier? e)) /\
           (Quantifier? e <==> ~(Var? e \/ App? e)))
  = ()

(* A closed App/Var (sub-)expression evaluates independently of the
   environment past the ambient variables it can see. For the
   App/Var cases this needs no assumption on the interpretation; the
   Quantifier case additionally requires that `interp_quant` respect
   extensional equality of `body_sem` (true of any interpretation
   that does not inspect `body_sem`'s source code, which is the only
   sensible kind), so it is recorded here as an explicit hypothesis
   on `i` rather than baked into `interpretation` itself. *)
let quant_extensional (#value:Type) (i:interpretation value) : prop =
  forall (qk:quantifier_kind) (bound_sorts:list sort) (f g:(list value -> value)).
    (forall (vs:list value{List.Tot.length vs = List.Tot.length bound_sorts}). f vs == g vs)
    ==> i.interp_quant qk bound_sorts f == i.interp_quant qk bound_sorts g

let rec lemma_closed_eval_env_irrelevant (#value:Type) (i:interpretation value)
    (e:expr) (depth:nat) (rho1 rho2:env value)
  : Lemma (requires quant_extensional i /\ closed_at depth e /\ (forall (j:nat). j < depth ==> rho1 j == rho2 j))
          (ensures eval i e rho1 == eval i e rho2)
  = match e with
    | Var idx _ -> ()
    | App f args -> lemma_closed_eval_args_env_irrelevant i args depth rho1 rho2
    | Quantifier qk bound_sorts body ->
      let n = List.Tot.length bound_sorts in
      let aux (vs:list value{List.Tot.length vs = n})
        : Lemma (eval i body (shift vs rho1) == eval i body (shift vs rho2))
        = let rho1' = shift vs rho1 in
          let rho2' = shift vs rho2 in
          let aux2 (j:nat{j < depth + n})
            : Lemma (rho1' j == rho2' j)
            = ()
          in
          FStar.Classical.forall_intro aux2;
          lemma_closed_eval_env_irrelevant i body (depth + n) rho1' rho2'
      in
      FStar.Classical.forall_intro aux

and lemma_closed_eval_args_env_irrelevant (#value:Type) (i:interpretation value)
    (args:list expr) (depth:nat) (rho1 rho2:env value)
  : Lemma (requires quant_extensional i /\ closed_at_args depth args /\ (forall (j:nat). j < depth ==> rho1 j == rho2 j))
          (ensures eval_args i args rho1 == eval_args i args rho2)
  = match args with
    | [] -> ()
    | a :: args' ->
      lemma_closed_eval_env_irrelevant i a depth rho1 rho2;
      lemma_closed_eval_args_env_irrelevant i args' depth rho1 rho2
