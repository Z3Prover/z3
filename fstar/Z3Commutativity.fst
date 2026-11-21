module Z3Commutativity

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality

include Z3CommutativitySyntax

(* The total value semantics follows the existing integer interpreter. *)
let arithmetic_model (i:interpretation value) : prop =
  forall (f:func_decl) (a b:expr) (rho:env value).
    {:pattern (eval i (App f [a; b]) rho)}
    arithmetic_decl f ==>
    eval i (App f [a; b]) rho ==
      (match eval i a rho, eval i b rho with
       | VInt x, VInt y -> VInt (if f.interp = Some op_plus then x + y else x * y)
       | _, _ -> VInt 0)

let lemma_eq_commutativity (i:interpretation value) (rho:env value)
                           (f:func_decl) (a b:expr)
  : Lemma (requires boolean_model i /\ eq_sound i /\ f == eq_decl (get_sort a) /\
                    get_sort a == get_sort b)
          (ensures eval i (App f [a; b]) rho == eval i (App f [b; a]) rho)
  = match eval i (App f [a; b]) rho, eval i (App f [b; a]) rho with
    | VBool _, VBool _ -> ()
    | _, _ -> ()

let lemma_add_commutativity (x y:int)
  : Lemma (x + y == y + x)
  = ()

let lemma_mul_commutativity (x y:int)
  : Lemma (x * y == y * x)
  = ()

let lemma_arithmetic_commutativity (i:interpretation value) (rho:env value)
                                   (f:func_decl) (a b:expr)
  : Lemma (requires arithmetic_model i /\ arithmetic_decl f /\
                    get_sort a == int_sort /\ get_sort b == int_sort)
          (ensures eval i (App f [a; b]) rho == eval i (App f [b; a]) rho)
  = match eval i a rho, eval i b rho with
    | VInt x, VInt y ->
      if f.interp = Some op_plus then lemma_add_commutativity x y
      else lemma_mul_commutativity x y
    | _, _ -> ()

let lemma_commutativity_step_sound (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires boolean_model i /\ eq_sound i /\ and_sound i /\ or_sound i /\
                    arithmetic_model i /\ commutativity_step a b)
          (ensures eval i a rho == eval i b rho)
  = match a, b with
    | App f [x; y], App g [u; v] ->
      if arithmetic_decl f then lemma_arithmetic_commutativity i rho f x y
      else if f.decl_name = "=" then lemma_eq_commutativity i rho f x y
      else
        (match eval i a rho, eval i b rho with
         | VBool _, VBool _ -> ()
         | _, _ -> ())
    | _, _ -> ()
