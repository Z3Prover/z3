(**
  RewriteCodeGen.fst

  F* tactic using Meta-F* reflection to extract Z3 C++ rewriter code from
  F* rewrite lemmas in FPARewriterRules.fst.

  Given a lemma such as:

    lemma_is_nan_ite:
      is_nan (if c then t else e) = (if c then is_nan t else is_nan e)

  Running `extract_rewrite (quote lemma_is_nan_ite)` produces:

    expr *c, *t, *e;
    if (m().is_ite(arg1, c, t, e)) {
        result = m().mk_ite(c, m_util.mk_is_nan(t), m_util.mk_is_nan(e));
        return BR_REWRITE2;
    }

  Approach:
  1. Use `tc` to get the type of the quoted lemma name.
  2. Strip universal quantifiers (Tv_Arrow chain), collecting parameter names.
  3. Extract the equality from the C_Lemma pre-condition.
  4. Decompose LHS into: top_fn(argument_pattern).
     The top_fn, e.g. is_nan, is the function whose rewriter method we extend.
     The argument pattern, e.g. if c then t else e, drives the C++ match.
  5. Decompose RHS into a construction expression.
  6. Emit C++ code for Z3's rewriter.

  Key F* reflection concepts used:
  - `inspect : term -> Tac term_view`  -- destructure a term
  - `Tv_App hd (arg, qual)`            -- curried function application
  - `Tv_Match scrutinee _ branches`    -- pattern match; if-then-else is a match on bool
  - `Tv_Arrow binder comp`             -- function/forall type
  - `C_Lemma pre post pats`            -- Lemma computation type
  - `Tv_FVar fv`                       -- free (top-level) variable
  - `Tv_BVar bv`                       -- bound variable, de Bruijn indexed
  - `tc env term`                      -- type-check a term, returning its type
**)

module RewriteCodeGen

open FStar.List.Tot
open FStar.Tactics.V2
open FStar.Reflection.V2

(* ================================================================
   Section 1: Intermediate Representation
   ================================================================ *)

(* Pattern recognized on the LHS, the argument to the top-level function *)
noeq type cpat =
  | PVar  : name:string -> cpat
  | PIte  : c:cpat -> t:cpat -> e:cpat -> cpat
  | PApp  : fn:string -> args:list cpat -> cpat

(* Expression to build on the RHS *)
noeq type cexpr =
  | EVar  : name:string -> cexpr
  | EIte  : c:cexpr -> t:cexpr -> e:cexpr -> cexpr
  | EApp  : fn:string -> args:list cexpr -> cexpr
  | EBool : v:bool -> cexpr

(* ================================================================
   Section 2: Reflection Helpers
   ================================================================ *)

(* Collect curried application spine:
   f a b c  to  (f, [(a,q1); (b,q2); (c,q3)])
   This undoes the nested Tv_App structure that F* uses for
   multi-argument applications. *)
let rec collect_app (t: term) : Tac (term & list argv) =
  match inspect_ln t with
  | Tv_App hd arg ->
    let (h, args) = collect_app hd in
    (h, args @ [arg])
  | _ -> (t, [])

(* Keep only explicit (non-implicit, non-meta) arguments.
   In F*, `is_nan #eb #sb x` has implicit args #eb, #sb and
   explicit arg x. We only care about explicit args for codegen. *)
let filter_explicit (args: list argv) : list term =
  List.Tot.map fst
    (List.Tot.filter (fun (_, q) -> Q_Explicit? q) args)

(* Get the short name of a free variable, last component of the path.
   E.g. "IEEE754.is_nan" to "is_nan" *)
let fv_short_name (t: term) : Tac (option string) =
  match inspect_ln t with
  | Tv_FVar fv ->
    (match List.Tot.rev (inspect_fv fv) with
     | last :: _ -> Some last
     | _ -> None)
  | _ -> None

(* Resolve a variable name from a term.
   In F* 2026, variables in lemma types returned by `tc env` may appear
   as named variables (Tv_Var namedv) rather than de Bruijn indices, so
   we first try the named view and fall back to de Bruijn lookup. *)
let var_name (idx_map: list (nat & string)) (offset: nat) (t: term) : Tac (option string) =
  (* Try named-view first: Tv_Var gives a directly named variable. *)
  (match FStar.Tactics.NamedView.inspect t with
   | FStar.Tactics.NamedView.Tv_Var nv ->
     let nm = unseal nv.ppname in
     Some nm
   | _ ->
     (* Fall back to de Bruijn lookup for variables still in closed form. *)
     match inspect_ln t with
     | Tv_BVar bv ->
       let bvv = inspect_bv bv in
       if bvv.index < offset then None
       else begin
         let adj : nat = bvv.index - offset in
         (match List.Tot.assoc #nat adj idx_map with
          | Some n -> Some n
          | None ->
            let pp = unseal bvv.ppname in
            print ("WARNING: var_name fallback for BVar index "
                   ^ string_of_int bvv.index ^ " (adj="
                   ^ string_of_int adj ^ "), using ppname '" ^ pp ^ "'");
            Some pp)
       end
     | _ -> None)

(* Detect if-then-else in reflected terms.
   In F*, `if c then t else e` desugars to:
     match c with | true -> t | (x:bool) -> e
   where the false branch uses Pat_Var (not Pat_Constant), adding an extra
   binder.  We therefore return the additional binder count for each branch
   body, so callers can adjust the de Bruijn offset accordingly:
     - then-branch (Pat_Constant): 0 extra binders
     - else-branch (Pat_Var):      1 extra binder *)
let try_ite (t: term) : Tac (option (term & nat & term & nat & term)) =
  match inspect_ln t with
  | Tv_Match scrutinee _ret branches ->
    (match branches with
     | [(pat_t, body_t); (pat_f, body_f)] ->
       let extra_t : nat = match pat_t with | Pat_Var _ _ -> 1 | _ -> 0 in
       let extra_f : nat = match pat_f with | Pat_Var _ _ -> 1 | _ -> 0 in
       Some (scrutinee, extra_t, body_t, extra_f, body_f)
     | _ -> None)
  | _ -> None

(* Unwrap `squash p` or `b2t p` to `p` if present.
   The Lemma postcondition is often wrapped in squash or b2t.
   In F* 2026, bool-valued propositions in Lemma postconditions are
   wrapped in `b2t` which coerces `bool` to `prop`. *)
let unwrap_squash (t: term) : Tac term =
  let (head, args) = collect_app t in
  match fv_short_name head with
  | Some "squash"
  | Some "b2t" ->
    (match filter_explicit args with | [inner] -> inner | _ -> t)
  | _ -> t

(* Extract an equality `a = b` from a term.
   F* represents `a = b` as either `eq2 #ty a b` or `op_Equality #ty a b`. *)
let extract_eq (t: term) : Tac (term & term) =
  let t' = unwrap_squash t in
  let (head, raw_args) = collect_app t' in
  let args = filter_explicit raw_args in
  match fv_short_name head, args with
  | Some "eq2",         [lhs; rhs]
  | Some "op_Equality", [lhs; rhs] -> (lhs, rhs)
  | name, _ ->
    fail ("expected equality, got head="
          ^ (match name with Some n -> n | None -> "?")
          ^ " with " ^ string_of_int (List.Tot.length args) ^ " explicit args")

(* Map in the Tac effect, since List.Tot.map is pure *)
let rec tac_map (#a #b: Type) (f: a -> Tac b) (l: list a) : Tac (list b) =
  match l with
  | [] -> []
  | x :: xs -> let y = f x in y :: tac_map f xs

(* ================================================================
   Section 3: Pattern & Expression Extraction
   ================================================================ *)

(* Extract a pattern from the LHS argument.
   Recognizes:
   - Variables (named or BVar)  -> PVar
   - if-then-else               -> PIte
   - Function applications      -> PApp *)
let rec extract_pat (m: list (nat & string)) (offset: nat) (t: term) : Tac cpat =
  match try_ite t with
  | Some (c, et, tb, ef, fb) ->
    let off_t : nat = offset + et in
    let off_f : nat = offset + ef in
    PIte (extract_pat m offset c) (extract_pat m off_t tb) (extract_pat m off_f fb)
  | None ->
    let (head, raw_args) = collect_app t in
    let args = filter_explicit raw_args in
    if List.Tot.length args > 0 then
      (match fv_short_name head with
       | Some fn -> PApp fn (tac_map (extract_pat m offset) args)
       | None ->
         (match var_name m offset head with
          | Some n -> PApp n (tac_map (extract_pat m offset) args)
          | None -> fail ("pattern app: cannot resolve head: " ^ term_to_string head)))
    else
      (match var_name m offset t with
       | Some n -> PVar n
       | None -> fail ("pattern: cannot recognize: " ^ term_to_string t))

(* Extract an expression from the RHS.
   Recognizes:
   - Variables (named or BVar)    -> EVar
   - Boolean literals              -> EBool
   - if-then-else                  -> EIte
   - Function applications (FVar) -> EApp *)
let rec extract_expr (m: list (nat & string)) (offset: nat) (t: term) : Tac cexpr =
  (* Check for boolean literals first *)
  (match inspect_ln t with
   | Tv_Const C_True  -> EBool true
   | Tv_Const C_False -> EBool false
   | _ ->
     match try_ite t with
     | Some (c, et, tb, ef, fb) ->
       let off_t : nat = offset + et in
       let off_f : nat = offset + ef in
       EIte (extract_expr m offset c) (extract_expr m off_t tb) (extract_expr m off_f fb)
     | None ->
       let (head, raw_args) = collect_app t in
       let args = filter_explicit raw_args in
       if List.Tot.length args > 0 then
         (match fv_short_name head with
          | Some fn -> EApp fn (tac_map (extract_expr m offset) args)
          | None -> fail ("expr: application head is not FVar: " ^ term_to_string head))
       else
         (match var_name m offset t with
          | Some n -> EVar n
          | None -> fail ("expr: cannot recognize: " ^ term_to_string t)))

(* ================================================================
   Section 4: Arrow Stripping & Index Map
   ================================================================ *)

(* Strip the Tv_Arrow chain from a lemma type:
     (#eb:pos) -> (#sb:pos) -> (c:bool) -> (t:float eb sb) -> (e:float eb sb)
       -> Lemma (...)
   Returns: parameter names [eb;sb;c;t;e] and the final computation, C_Lemma. *)
let rec strip_arrows (t: term) : Tac (list string & comp) =
  match inspect_ln t with
  | Tv_Arrow binder c ->
    let name = unseal (inspect_binder binder).ppname in
    (match inspect_comp c with
     | C_Total ret ->
       let (names, final_c) = strip_arrows ret in
       (name :: names, final_c)
     | _ -> ([name], c))
  | _ -> fail ("expected arrow type, got: " ^ term_to_string t)

(* Build de Bruijn index to name map.
   Binders collected outer-to-inner: [eb; sb; c; t; e]
   De Bruijn indices are inner-to-outer: e=0, t=1, c=2, sb=3, eb=4
   So we reverse the list and pair with ascending indices. *)
let build_idx_map (names: list string) : Tot (list (nat & string)) =
  let rev_names = List.Tot.rev names in
  let rec aux (i: nat) (ns: list string) : Tot (list (nat & string)) (decreases ns) =
    match ns with
    | [] -> []
    | n :: rest -> (i, n) :: aux (i + 1) rest
  in
  aux 0 rev_names

(* ================================================================
   Section 5: C++ Code Generation
   ================================================================ *)

(* Map an F* IEEE754 function name to the corresponding Z3 C++ builder.
   The "is_*" predicates in IEEE754.fst correspond directly to
   fpa_util::mk_is_* in Z3's C++ API. *)
let cpp_builder_name (fn: string) : string =
  match fn with
  | "is_nan"      -> "m_util.mk_is_nan"
  | "is_inf"      -> "m_util.mk_is_inf"
  | "is_normal"   -> "m_util.mk_is_normal"
  | "is_negative" -> "m_util.mk_is_negative"
  | "is_positive" -> "m_util.mk_is_positive"
  | "is_zero"     -> "m_util.mk_is_zero"
  | _             -> "m_util.mk_" ^ fn

(* Collect all variable names from a pattern (for C++ declarations) *)
let rec pat_vars (p: cpat) : Tot (list string) (decreases p) =
  match p with
  | PVar n       -> [n]
  | PIte c t e   -> pat_vars c @ pat_vars t @ pat_vars e
  | PApp _ args  -> pat_vars_list args

and pat_vars_list (ps: list cpat) : Tot (list string) (decreases ps) =
  match ps with
  | []      -> []
  | x :: xs -> pat_vars x @ pat_vars_list xs

(* Generate: expr *c, *t, *e; *)
let gen_decls (p: cpat) : string =
  let vars = pat_vars p in
  match vars with
  | []  -> ""
  | [v] -> "    expr *" ^ v ^ ";"
  | _   -> "    expr *" ^ FStar.String.concat ", *" vars ^ ";"

(* Generate the C++ condition that matches the LHS pattern.
   For PIte(c,t,e): m().is_ite(arg1, c, t, e) *)
let gen_condition (arg: string) (p: cpat) : string =
  match p with
  | PIte (PVar c) (PVar t) (PVar e) ->
    "m().is_ite(" ^ arg ^ ", " ^ c ^ ", " ^ t ^ ", " ^ e ^ ")"
  | PApp fn args ->
    (match fn, args with
     | "to_fp_of_int", [PVar _rm; PVar x] ->
       "m_util.is_to_fp(" ^ arg ^ ") && to_app(" ^ arg ^ ")->get_num_args() == 2"
       ^ " /* rm=" ^ _rm ^ ", int_expr=" ^ x ^ " */"
     | _ ->
       "/* TODO: extend gen_condition for " ^ fn ^ " */")
  | PVar _ -> "true /* variable pattern, always matches */"
  | _ -> "/* TODO: extend gen_condition for nested patterns */"

(* Generate a C++ expression from the RHS IR *)
let rec gen_rhs_expr (e: cexpr) : Tot string (decreases e) =
  match e with
  | EVar  n       -> n
  | EBool true    -> "m().mk_true()"
  | EBool false   -> "m().mk_false()"
  | EIte  c t e   ->
    "m().mk_ite(" ^ gen_rhs_expr c ^ ", "
                  ^ gen_rhs_expr t ^ ", "
                  ^ gen_rhs_expr e ^ ")"
  | EApp fn args  ->
    cpp_builder_name fn ^ "("
    ^ gen_rhs_expr_list args ^ ")"

and gen_rhs_expr_list (es: list cexpr) : Tot string (decreases es) =
  (* Comma-separated list for C++ function arguments.  Empty list yields ""
     so EApp fn [] produces fn_name(), which is valid C++ for zero-arg calls
     (e.g. builder helper functions that take no explicit arguments). *)
  match es with
  | []      -> ""
  | [e]     -> gen_rhs_expr e
  | e :: rest -> gen_rhs_expr e ^ ", " ^ gen_rhs_expr_list rest

(* Generate the complete C++ rewrite case *)
let gen_cpp (top_fn: string) (arg: string) (pat: cpat) (rhs: cexpr) : string =
  let decls = gen_decls pat in
  let cond  = gen_condition arg pat in
  let body  = gen_rhs_expr rhs in
  (if FStar.String.length decls > 0 then decls ^ "\n" else "")
  ^ "    if (" ^ cond ^ ") {\n"
  ^ "        result = " ^ body ^ ";\n"
  ^ "        return BR_REWRITE2;\n"
  ^ "    }"

(* ================================================================
   Section 6: Main Extraction Entry Point
   ================================================================ *)

(**
  Given a quoted lemma name, extract and return C++ rewriter code.
  The generated code is a self-contained if-block that can be placed
  directly inside the corresponding mk_* function in fpa_rewriter.cpp.

  Usage:
    run_tactic (fun () -> print (extract_rewrite (quote lemma_is_nan_ite)))

  or to splice a comment into an F* file:
    let _ = assert_norm (True);
            run_tactic (fun () -> print (extract_rewrite (quote lemma_is_nan_ite)))

  The lemma must have the shape:
    let lemma_<name> (#eb #sb: pos) ... : Lemma (top_fn LHS_pattern = RHS) = ...

  where top_fn is an IEEE754 classification predicate (is_nan, is_inf, is_normal).

  For the argument name passed to the generated is_ite / is_to_fp check,
  "arg1" is assumed (the standard name in fpa_rewriter.cpp mk_* functions).
**)
let extract_rewrite (lemma: term) : Tac string =
  let env = top_env () in
  let ty = tc env lemma in

  (* 1. Strip forall binders, collect parameter names *)
  let (param_names, final_comp) = strip_arrows ty in
  let idx_map = build_idx_map param_names in

  (* 2. Get the equality from the Lemma postcondition.
     For `Lemma P`, the comp is C_Lemma l_True (fun _ -> b2t P) [].
     The postcondition is a function taking the return value as argument.
     We peel off the leading Tv_Abs to get the raw proposition.
     Inside the abs body, all de Bruijn indices are shifted by 1 relative
     to the outer scope, so we pass offset=1 to extract_pat/extract_expr. *)
  let (post, post_offset) =
    match inspect_comp final_comp with
    | C_Lemma _ post _ ->
      (match inspect_ln post with
       | Tv_Abs _ body -> (body, 1)
       | _ -> (post, 0))
    | _ -> fail "expected Lemma computation type" in

  (* 3. Extract LHS = RHS from the postcondition *)
  let (lhs, rhs) = extract_eq post in

  (* 4. Decompose LHS: top_fn(argument_pattern).
     The top_fn is the IEEE754 classification predicate whose
     mk_* method we are extending in fpa_rewriter.
     We expect exactly one explicit argument on the LHS. *)
  let (head, raw_args) = collect_app lhs in
  let args = filter_explicit raw_args in
  let top_fn =
    match fv_short_name head with
    | Some n -> n
    | None -> fail ("LHS head is not a free variable: " ^ term_to_string head) in
  let arg_term =
    match args with
    | [a] -> a
    | _ ->
      fail ("expected exactly one explicit arg on LHS, got "
            ^ string_of_int (List.Tot.length args)
            ^ " for top_fn=" ^ top_fn) in

  (* 5. Extract the argument pattern and the RHS expression *)
  let pat      = extract_pat  idx_map post_offset arg_term in
  let rhs_expr = extract_expr idx_map post_offset rhs in

  (* 6. Emit C++ code.
     "arg1" is the standard name for the argument in mk_* functions of
     fpa_rewriter.cpp, e.g. br_status fpa_rewriter::mk_is_nan(expr *arg1, ...). *)
  gen_cpp top_fn "arg1" pat rhs_expr


(* ================================================================
   Section 7: Extraction Examples
   ================================================================

   Run these with:
     fstar.exe --include . IEEE754.fst FPARewriterRules.fst RewriteCodeGen.fst

   The `run_tactic (fun () -> print ...)` calls emit the generated C++ to
   stdout during F* typechecking.  The output can be captured and placed
   directly in fpa_rewriter_rules.h (wrapped in an appropriate #define).

   Expected output for lemma_is_nan_ite:
   ================================================================
     expr *c, *t, *e;
     if (m().is_ite(arg1, c, t, e)) {
         result = m().mk_ite(c, m_util.mk_is_nan(t), m_util.mk_is_nan(e));
         return BR_REWRITE2;
     }
   ================================================================

   Expected output for lemma_is_inf_ite:
   ================================================================
     expr *c, *t, *e;
     if (m().is_ite(arg1, c, t, e)) {
         result = m().mk_ite(c, m_util.mk_is_inf(t), m_util.mk_is_inf(e));
         return BR_REWRITE2;
     }
   ================================================================

   Expected output for lemma_is_normal_ite:
   ================================================================
     expr *c, *t, *e;
     if (m().is_ite(arg1, c, t, e)) {
         result = m().mk_ite(c, m_util.mk_is_normal(t), m_util.mk_is_normal(e));
         return BR_REWRITE2;
     }
   ================================================================
*)

open FPARewriterRules

(* Helper: extract and print one lemma's C++ rewrite rule. *)
let print_rewrite (label: string) (lemma: term) : Tac unit =
  print ("\n=== " ^ label ^ " ===\n");
  print (extract_rewrite lemma)

(* Construct a term reference to a top-level name in FPARewriterRules
   without instantiating implicit arguments.  Using pack_fv avoids the
   elaboration that quote performs, which in F* 2026 fails for polymorphic
   lemmas whose implicit type arguments (eb, sb: pos) cannot be inferred
   from the call site. *)
let lemma_ref (name: string) : term =
  pack_ln (Tv_FVar (pack_fv ["FPARewriterRules"; name]))

(* Demonstrate extraction of the three ite-pushthrough lemmas.
   Running this file with F* prints the generated C++ for each rule. *)
let _ =
  run_tactic (fun () ->
    iter (fun (label, lemma) -> print_rewrite label lemma)
      [ ("lemma_is_nan_ite",    lemma_ref "lemma_is_nan_ite");
        ("lemma_is_inf_ite",    lemma_ref "lemma_is_inf_ite");
        ("lemma_is_normal_ite", lemma_ref "lemma_is_normal_ite") ])
