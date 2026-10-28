module NullAstGuards
(* Semantic model of the PR guards. AST pointer: Null | Sort | Expr with predicate tags. *)
type ast =
  | Null
  | SortAst
  | Expr : isfp:bool -> isrm:bool -> isbv:bool -> isnum:bool -> isalg:bool -> isfpnum:bool -> ast

(* "safe to call to_expr(a)" *)
let safe_expr (a:ast) : bool = Expr? a

(* is_fp / is_rm / is_bv: a != nullptr && is_expr(a) && pred(to_expr(a)) *)
let is_fp (a:ast) : bool = (not (Null? a)) && safe_expr a && (Expr?.isfp a)
let is_rm (a:ast) : bool = (not (Null? a)) && safe_expr a && (Expr?.isrm a)
let is_bv (a:ast) : bool = (not (Null? a)) && safe_expr a && (Expr?.isbv a)

(* O1: guards never accept Null/sort, so subsequent to_expr is safe *)
let o1 (a:ast) : Lemma (ensures (is_fp a ==> Expr? a) /\ (is_rm a ==> Expr? a) /\ (is_bv a ==> Expr? a)
                                /\ (Null? a ==> not (is_fp a || is_rm a || is_bv a))) = ()

(* O2: Z3_algebraic_is_value. result = (err, value) *)
let alg_core (a:ast) : bool = (not (Null? a)) && safe_expr a && (Expr?.isnum a || Expr?.isalg a)
let alg_is_value (a:ast) : bool & bool =
  if Null? a then (true, false) else (false, alg_core a)
let o2 (a:ast) : Lemma (ensures (Null? a ==> alg_is_value a = (true,false))
                              /\ (not (Null? a) ==> fst (alg_is_value a) = false)
                              /\ (snd (alg_is_value a) ==> Expr? a /\ (Expr?.isnum a || Expr?.isalg a))) = ()

(* O3: Z3_fpa_is_numeral_* : guard !t || !is_expr(t) || !is_numeral => error; no error => numeral expr *)
let fpa_pred (a:ast) : bool & bool =
  if Null? a || not (safe_expr a) || not (Expr?.isfpnum a) then (true,false) else (false,true)
let o3 (a:ast) : Lemma (ensures (Null? a ==> fst (fpa_pred a)) /\ (not (fst (fpa_pred a)) ==> Expr? a /\ Expr?.isfpnum a)) = ()

(* Witness: base-code guard order (to_expr before null check) is only defined on Expr,
   so for Null the old is_fp has no defined value; new one is total. *)
let new_is_fp_total (a:ast) : Lemma (is_fp Null = false /\ is_fp SortAst = false) = ()
