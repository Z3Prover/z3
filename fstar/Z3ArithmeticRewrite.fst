module Z3ArithmeticRewrite

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open FStar.Real
open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module A = Z3LinearArithmeticAst
module E = Z3LinearArithmeticEmbed
module P = Z3LinearArithmeticTheory

let zero_polynomial (p:A.poly) : bool =
  p.cst = 0 && P.all_zero (P.collect p.mono [])

let same_polynomial (p q:A.poly) : bool =
  zero_polynomial (P.add p (P.scale (-1) 1 q))

let constant_truth (p:A.contribution) : option bool =
  if P.all_zero (P.collect p.poly.mono [])
  then Some (if p.strict then p.poly.cst < 0 else p.poly.cst <= 0)
  else None

let same_constraint (p q:A.contribution) : bool =
  match constant_truth p, constant_truth q with
  | Some x, Some y -> x = y
  | _, _ -> p.strict = q.strict && same_polynomial p.poly q.poly

let not_decl : func_decl =
  { decl_name = "not"; domain = [bool_sort]; range = bool_sort;
    interp = Some op_not; int_params = [] }

let rec constraint_of (fuel:nat) (positive:bool) (e:expr)
  : Tot (option A.contribution) (decreases fuel) =
  if fuel = 0 then None
  else if e = true_expr || e = false_expr then
    Some { P.poly = P.constant (if (e = true_expr) = positive then 0 else 1) 1;
           strict = false }
  else match e with
  | App f [a] ->
    if f = not_decl && get_sort a = bool_sort
    then constraint_of (fuel - 1) (not positive) a else None
  | _ ->
    (match A.comparison e with
     | Some (r, a, b) ->
       if r = A.Eq then None
       else (match A.linearize 64 a, A.linearize 64 b with
       | Some pa, Some pb ->
         let p, strict = A.oriented positive r pa pb in
         Some { P.poly = p; strict = strict }
       | _, _ -> None)
     | None -> None)

let boolean_equivalent (a b:expr) : bool =
  get_sort a = bool_sort && get_sort b = bool_sort &&
  (match constraint_of 16 true a, constraint_of 16 true b with
   | Some p, Some q -> same_constraint p q
   | _, _ -> false)

let integer_equivalent (a b:expr) : bool =
  get_sort a = A.int_s && get_sort b = A.int_s &&
  (match A.linearize 64 a, A.linearize 64 b with
   | Some p, Some q -> same_polynomial p q
   | _, _ -> false)

let equivalent (a b:expr) : bool =
  boolean_equivalent a b || integer_equivalent a b

let lemma_zero_polynomial (p:A.poly) (rho:expr -> real)
  : Lemma (requires zero_polynomial p) (ensures P.value p rho == 0.0R) =
  P.lemma_collect p.mono [] rho;
  P.lemma_all_zero (P.collect p.mono []) rho

let lemma_same_polynomial (p q:A.poly) (x y:real) (rho:expr -> real)
  : Lemma (requires same_polynomial p q /\ E.denotes p x rho /\ E.denotes q y rho)
          (ensures x == y) =
  E.lemma_denotes_negative q y rho;
  E.lemma_denotes_add p (P.scale (-1) 1 q) x (0.0R -. y) rho;
  lemma_zero_polynomial (P.add p (P.scale (-1) 1 q)) rho;
  assert (of_int (P.add p (P.scale (-1) 1 q)).denom >. 0.0R)

let lemma_constant_truth (p:A.contribution) (rho:expr -> real) (b:bool)
  : Lemma (requires constant_truth p == Some b)
          (ensures P.holds p rho <==> b) =
  P.lemma_collect p.poly.mono [] rho;
  P.lemma_all_zero (P.collect p.poly.mono []) rho

let lemma_same_constraint (p q:A.contribution) (rho:expr -> real)
  : Lemma (requires same_constraint p q)
          (ensures P.holds p rho <==> P.holds q rho) =
  match constant_truth p, constant_truth q with
  | Some x, Some y ->
    lemma_constant_truth p rho x;
    lemma_constant_truth q rho y
  | _, _ ->
    let x = P.value p.poly rho /. of_int p.poly.denom in
    let y = P.value q.poly rho /. of_int q.poly.denom in
    assert (E.denotes p.poly x rho /\ E.denotes q.poly y rho);
    lemma_same_polynomial p.poly q.poly x y rho;
    assert (of_int p.poly.denom >. 0.0R /\ of_int q.poly.denom >. 0.0R)

(* These are local value-typing premises, not the global all-environments
   typing contract used by the older embedding. *)
let rec boolean_values (i:interpretation value) (rho:env value) (e:expr)
  : Tot prop (decreases e) =
  VBool? (eval i e rho) /\
  (match e with
   | App f [a] -> if f = not_decl then boolean_values i rho a else True
   | _ -> True)

let lemma_scaled_relation (positive:bool) (rel:A.relation) (d:pos) (v x y:real)
  : Lemma (requires rel <> A.Eq /\ v == of_int d *. E.difference positive rel x y)
          (ensures
            (if (if positive then rel = A.Lt || rel = A.Gt else rel = A.Le || rel = A.Ge)
             then v <. 0.0R else v <=. 0.0R) <==>
            (if positive then E.numeric_relation rel x y else ~(E.numeric_relation rel x y))) =
  assert (of_int d >. 0.0R);
  match rel with
  | A.Le | A.Lt | A.Ge | A.Gt | A.Eq -> if positive then () else ()

#push-options "--fuel 4"

let rec lemma_constraint_of (fuel:nat) (positive:bool) (e:expr)
                            (p:A.contribution)
                            (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ not_sound i /\ true_sound i /\ false_sound i /\
                    boolean_values i rho e /\ constraint_of fuel positive e == Some p)
          (ensures P.holds p (E.valuation i nu rho) <==>
                   (if positive then lit_true i rho e else ~(lit_true i rho e)))
          (decreases fuel) =
  if e = true_expr || e = false_expr then ()
  else match e with
  | App f [a] ->
    lemma_constraint_of (fuel - 1) (not positive) a p i nu rho;
    (match eval i a rho with VBool _ -> () | _ -> ())
  | _ ->
    (match A.comparison e with
     | Some (r, a, b) ->
       assert (r <> A.Eq);
       let pa = Some?.v (A.linearize 64 a) in
       let pb = Some?.v (A.linearize 64 b) in
       assert (p.poly == fst (A.oriented positive r pa pb) /\
               p.strict == snd (A.oriented positive r pa pb));
       E.lemma_linearize 64 a pa i nu rho;
       E.lemma_linearize 64 b pb i nu rho;
       E.lemma_oriented positive r pa pb (nu (eval i a rho)) (nu (eval i b rho))
                         (E.valuation i nu rho);
       lemma_scaled_relation positive r p.poly.denom
         (P.value p.poly (E.valuation i nu rho)) (nu (eval i a rho)) (nu (eval i b rho));
       assert (lit_true i rho e <==>
               E.numeric_relation r (nu (eval i a rho)) (nu (eval i b rho)))
     | None -> ())

#pop-options

let lemma_boolean_equivalent (a b:expr) (i:interpretation value)
                             (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ not_sound i /\ true_sound i /\ false_sound i /\
                    boolean_values i rho a /\ boolean_values i rho b /\ boolean_equivalent a b)
          (ensures eval i a rho == eval i b rho) =
  let p = Some?.v (constraint_of 16 true a) in
  let q = Some?.v (constraint_of 16 true b) in
  lemma_constraint_of 16 true a p i nu rho;
  lemma_constraint_of 16 true b q i nu rho;
  lemma_same_constraint p q (E.valuation i nu rho);
  match eval i a rho, eval i b rho with
  | VBool _, VBool _ -> ()
  | _, _ -> ()

let lemma_integer_equivalent (a b:expr) (i:interpretation value)
                             (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ VInt? (eval i a rho) /\
                    VInt? (eval i b rho) /\ integer_equivalent a b)
          (ensures eval i a rho == eval i b rho) =
  let p = Some?.v (A.linearize 64 a) in
  let q = Some?.v (A.linearize 64 b) in
  E.lemma_linearize 64 a p i nu rho;
  E.lemma_linearize 64 b q i nu rho;
  lemma_same_polynomial p q (nu (eval i a rho)) (nu (eval i b rho)) (E.valuation i nu rho);
  match eval i a rho, eval i b rho with
  | VInt _, VInt _ -> ()
  | _, _ -> ()

let rec lemma_boolean_values (fuel:nat) (positive:bool)
                             (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires Z3ObservationalEquality.boolean_model i /\ get_sort e == bool_sort /\
                    Some? (constraint_of fuel positive e))
          (ensures boolean_values i rho e)
          (decreases fuel) =
  if e = true_expr || e = false_expr then ()
  else match e with
  | App f [a] -> lemma_boolean_values (fuel - 1) (not positive) i rho a
  | _ -> ()

let lemma_equivalent_with_numeric_model (a b:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    Z3ObservationalEquality.boolean_model i /\
                    not_sound i /\ true_sound i /\ false_sound i /\ equivalent a b)
          (ensures eval i a rho == eval i b rho) =
  let aux (nu:value -> real) : Lemma
      (requires E.numeric_model i nu) (ensures eval i a rho == eval i b rho) =
    if boolean_equivalent a b then (
      lemma_boolean_values 16 true i rho a;
      lemma_boolean_values 16 true i rho b;
      lemma_boolean_equivalent a b i nu rho)
    else lemma_integer_equivalent a b i nu rho
  in
  FStar.Classical.exists_elim (eval i a rho == eval i b rho)
    #(value -> real) #(fun nu -> E.numeric_model i nu) () (fun nu -> aux nu)
