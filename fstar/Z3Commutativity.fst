module Z3Commutativity

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality

let int_sort : sort = BaseSort "Int"

let arithmetic_decl (f:func_decl) : bool =
  f.domain = [int_sort; int_sort] && f.range = int_sort && f.int_params = [] &&
  ((f.decl_name = "+" && f.interp = Some op_plus) ||
   (f.decl_name = "*" && f.interp = Some op_mul))

let commutative_decl (f:func_decl) : bool =
  (match f.domain with
   | [s; t] -> s = t && f = eq_decl s
   | _ -> false) ||
  (f.domain = [bool_sort; bool_sort] && f.range = bool_sort && f.int_params = [] &&
   ((f.decl_name = "and" && f.interp = Some op_and) ||
    (f.decl_name = "or" && f.interp = Some op_or))) ||
  arithmetic_decl f

let commutativity_step (a b:expr) : bool =
  match a, b with
  | App f [x; y], App g [u; v] ->
    f = g && commutative_decl f && f.domain = [get_sort x; get_sort y] &&
    x = v && y = u
  | _, _ -> false

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
