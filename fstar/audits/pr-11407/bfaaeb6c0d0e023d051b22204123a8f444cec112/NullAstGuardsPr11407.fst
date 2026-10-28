module NullAstGuardsPr11407
(* Abstract model of the guards in the PR head. Pointer is Null, a Sort, or an Expr with
   predicate tags. Dereferencing as expr (to_expr) is "safe" only for Expr. *)
type ast =
  | Null
  | SortAst
  | Expr : isfp:bool -> isrm:bool -> isbv:bool -> isreal:bool -> isint:bool
           -> isnum:bool -> isalg:bool -> isfpnum:bool -> ast

let is_expr (a:ast) : bool = Expr? a
(* The effect of to_expr(a) followed by a predicate: only defined on Expr. *)
let on_expr (a:ast) (p:(a:ast{Expr? a}) -> bool) : option bool =
  match a with | Expr .. -> Some (p a) | _ -> None

(* G1: static helpers is_fp/is_rm/is_bv: a != nullptr && is_expr(a) && pred *)
let guard (a:ast) (p:(a:ast{Expr? a}) -> bool) : bool =
  (not (Null? a)) && is_expr a && (match a with | Expr .. -> p a | _ -> false)
let is_fp (a:ast) = guard a (fun e -> Expr?.isfp e)
let is_rm (a:ast) = guard a (fun e -> Expr?.isrm e)
let is_bv (a:ast) = guard a (fun e -> Expr?.isbv e)

let g1 (a:ast) (p:(a:ast{Expr? a}) -> bool)
  : Lemma (ensures (guard a p ==> Expr? a) /\ (Null? a ==> not (guard a p)) /\ (SortAst? a ==> not (guard a p))) = ()

(* G2: Z3_algebraic_is_value: CHECK_NON_NULL sets error, returns false; otherwise core. *)
let alg_core (a:ast) : bool =
  (not (Null? a)) && is_expr a && (match a with | Expr .. -> Expr?.isnum a || Expr?.isalg a | _ -> false)
let alg_is_value (a:ast) : bool & bool = if Null? a then (true, false) else (false, alg_core a)
let g2 (a:ast)
  : Lemma (ensures (Null? a ==> alg_is_value a == (true,false))
                /\ (not (Null? a) ==> fst (alg_is_value a) == false)
                /\ (snd (alg_is_value a) ==> Expr? a /\ (Expr?.isnum a \/ Expr?.isalg a))) = ()

(* G3: Z3_mk_fpa_to_fp_real / Z3_mk_fpa_to_fp_int_real argument guards.
   Condition accepted (no error) iff every AST arg passes its guard. Returns true if call proceeds. *)
let real_guard (t:ast) : bool = (not (Null? t)) && is_expr t && (match t with | Expr .. -> Expr?.isreal t | _ -> false)
let int_guard (t:ast) : bool = (not (Null? t)) && is_expr t && (match t with | Expr .. -> Expr?.isint t | _ -> false)
let to_fp_real_ok (rm t:ast) : bool = is_rm rm && real_guard t
let to_fp_int_real_ok (rm e s:ast) : bool = is_rm rm && int_guard e && real_guard s
let g3 (rm t e s:ast)
  : Lemma (ensures (to_fp_real_ok rm t ==> Expr? rm /\ Expr? t)
                /\ (to_fp_int_real_ok rm e s ==> Expr? rm /\ Expr? e /\ Expr? s)
                /\ ((Null? rm \/ Null? t) ==> not (to_fp_real_ok rm t))
                /\ ((Null? rm \/ Null? e \/ Null? s) ==> not (to_fp_int_real_ok rm e s))) = ()

(* Exclusion witness for regression: a sort arg passed where an expr is expected is rejected. *)
let _ = assert_norm (not (to_fp_real_ok SortAst (Expr false false false true false false false false)))
