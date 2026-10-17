module Z3ArithmeticRewrite

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open FStar.Real
open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module B = Z3BooleanRewrite
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

let numeric_equivalent (a b:expr) : bool =
  A.numeric_sort (get_sort a) && get_sort a = get_sort b &&
  (match A.linearize 64 a, A.linearize 64 b with
   | Some p, Some q -> same_polynomial p q
   | _, _ -> false)

let equation_of (e:expr) : option A.poly =
  match A.comparison e with
  | Some (A.Eq, a, b) ->
    (match A.linearize 64 a, A.linearize 64 b with
     | Some p, Some q -> Some (P.add p (P.scale (-1) 1 q))
     | _, _ -> None)
  | _ -> None

let equation_equivalent (a b:expr) : bool =
  match equation_of a, equation_of b with
  | Some p, Some q -> same_polynomial p q
  | _, _ -> false

let split_equation (e bounds:expr) : bool =
  match equation_of e, bounds with
  | Some p, App f [lower; upper] ->
    B.connective_app B.Conjunction f [lower; upper] &&
    (match constraint_of 16 true lower, constraint_of 16 true upper with
     | Some l, Some u ->
       same_constraint l { P.poly = p; strict = false } &&
       same_constraint u { P.poly = P.scale (-1) 1 p; strict = false }
     | _, _ -> false)
  | _, _ -> false

let triangle_equality (e:expr) : bool =
  match e with
  | App f [eq; App lf [l]; App uf [u]] ->
    B.connective_app B.Disjunction f [eq; App lf [l]; App uf [u]] &&
    lf = not_decl && uf = not_decl &&
    split_equation eq (App (B.connective_decl B.Conjunction [l; u]) [l; u])
  | _ -> false

let equivalent (a b:expr) : bool =
  boolean_equivalent a b || numeric_equivalent a b ||
  equation_equivalent a b || split_equation a b || split_equation b a

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

let lemma_numeric_values_equal (a b:expr) (i:interpretation value)
                               (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ A.numeric_sort (get_sort a) /\
                    get_sort a == get_sort b /\ nu (eval i a rho) == nu (eval i b rho))
          (ensures eval i a rho == eval i b rho) =
  if get_sort a = A.real_s then ()
  else match eval i a rho, eval i b rho with
  | VInt _, VInt _ -> ()
  | _, _ -> ()

let lemma_numeric_equivalent (a b:expr) (i:interpretation value)
                             (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ numeric_equivalent a b)
          (ensures eval i a rho == eval i b rho) =
  let p = Some?.v (A.linearize 64 a) in
  let q = Some?.v (A.linearize 64 b) in
  E.lemma_linearize 64 a p i nu rho;
  E.lemma_linearize 64 b q i nu rho;
  lemma_same_polynomial p q (nu (eval i a rho)) (nu (eval i b rho)) (E.valuation i nu rho);
  lemma_numeric_values_equal a b i nu rho

let lemma_equation_of (e:expr) (p:A.poly) (i:interpretation value)
                      (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ eq_sound i /\ equation_of e == Some p)
          (ensures lit_true i rho e <==> P.value p (E.valuation i nu rho) == 0.0R) =
  match A.comparison e with
  | Some (A.Eq, a, b) ->
    let pa = Some?.v (A.linearize 64 a) in
    let pb = Some?.v (A.linearize 64 b) in
    let x = nu (eval i a rho) in
    let y = nu (eval i b rho) in
    E.lemma_linearize 64 a pa i nu rho;
    E.lemma_linearize 64 b pb i nu rho;
    E.lemma_denotes_negative pb y (E.valuation i nu rho);
    E.lemma_denotes_add pa (P.scale (-1) 1 pb) x (0.0R -. y) (E.valuation i nu rho);
    assert (of_int p.denom >. 0.0R);
    FStar.Classical.impl_intro #(x == y) #(eval i a rho == eval i b rho)
      (fun _ -> lemma_numeric_values_equal a b i nu rho);
    (match e with App _ [_; _] -> () | _ -> ())
  | _ -> ()

let lemma_equation_equivalent (a b:expr) (i:interpretation value)
                              (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ eq_sound i /\
                    Z3ObservationalEquality.boolean_model i /\ equation_equivalent a b)
          (ensures eval i a rho == eval i b rho) =
  let p = Some?.v (equation_of a) in
  let q = Some?.v (equation_of b) in
  let rv = E.valuation i nu rho in
  lemma_equation_of a p i nu rho;
  lemma_equation_of b q i nu rho;
  let x = P.value p rv /. of_int p.denom in
  let y = P.value q rv /. of_int q.denom in
  lemma_same_polynomial p q x y rv;
  assert (of_int p.denom >. 0.0R /\ of_int q.denom >. 0.0R);
  match eval i a rho, eval i b rho with
  | VBool _, VBool _ -> ()
  | _, _ -> ()

let lemma_split_equation (e bounds:expr) (i:interpretation value)
                         (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ eq_sound i /\ and_sound i /\
                    not_sound i /\ true_sound i /\ false_sound i /\
                    Z3ObservationalEquality.boolean_model i /\ split_equation e bounds)
          (ensures eval i e rho == eval i bounds rho) =
  match bounds with
  | App f [lower; upper] ->
    let p = Some?.v (equation_of e) in
    let l = Some?.v (constraint_of 16 true lower) in
    let u = Some?.v (constraint_of 16 true upper) in
    let rv = E.valuation i nu rho in
    lemma_equation_of e p i nu rho;
    lemma_boolean_values 16 true i rho lower;
    lemma_boolean_values 16 true i rho upper;
    lemma_constraint_of 16 true lower l i nu rho;
    lemma_constraint_of 16 true upper u i nu rho;
    lemma_same_constraint l { P.poly = p; strict = false } rv;
    lemma_same_constraint u { P.poly = P.scale (-1) 1 p; strict = false } rv;
    P.lemma_scale (-1) 1 p rv;
    assert (P.value (P.scale (-1) 1 p) rv == 0.0R -. P.value p rv);
    assert (lit_true i rho lower <==> P.value p rv <=. 0.0R);
    assert (lit_true i rho upper <==> 0.0R <=. P.value p rv);
    assert (lit_true i rho e <==> (lit_true i rho lower /\ lit_true i rho upper));
    assert (lit_true i rho bounds <==> conj_holds i rho [lower; upper]);
    assert (lit_true i rho e <==> lit_true i rho bounds);
    (match eval i e rho, eval i bounds rho with
     | VBool _, VBool _ -> ()
     | _, _ -> ())
  | _ -> ()

let lemma_triangle_equality (e:expr) (i:interpretation value)
                            (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ eq_sound i /\ and_sound i /\ or_sound i /\
                    not_sound i /\ true_sound i /\ false_sound i /\
                    Z3ObservationalEquality.boolean_model i /\ triangle_equality e)
          (ensures lit_true i rho e) =
  match e with
  | App f [eq; App lf [l]; App uf [u]] ->
    let bounds = App (B.connective_decl B.Conjunction [l; u]) [l; u] in
    lemma_split_equation eq bounds i nu rho;
    (match eval i l rho, eval i u rho with
     | VBool _, VBool _ -> ()
     | _, _ -> ())
  | _ -> ()

let lemma_equivalent_with_numeric_model (a b:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    Z3ObservationalEquality.boolean_model i /\
                    not_sound i /\ true_sound i /\ false_sound i /\ eq_sound i /\
                    and_sound i /\ equivalent a b)
          (ensures eval i a rho == eval i b rho) =
  let aux (nu:value -> real) : Lemma
      (requires E.numeric_model i nu) (ensures eval i a rho == eval i b rho) =
    if boolean_equivalent a b then (
      lemma_boolean_values 16 true i rho a;
      lemma_boolean_values 16 true i rho b;
      lemma_boolean_equivalent a b i nu rho)
    else if numeric_equivalent a b then lemma_numeric_equivalent a b i nu rho
    else if equation_equivalent a b then lemma_equation_equivalent a b i nu rho
    else if split_equation a b then lemma_split_equation a b i nu rho
    else lemma_split_equation b a i nu rho
  in
  FStar.Classical.exists_elim (eval i a rho == eval i b rho)
    #(value -> real) #(fun nu -> E.numeric_model i nu) () (fun nu -> aux nu)

let lemma_triangle_with_numeric_model (e:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    Z3ObservationalEquality.boolean_model i /\ eq_sound i /\
                    and_sound i /\ or_sound i /\ not_sound i /\
                    true_sound i /\ false_sound i /\ triangle_equality e)
          (ensures lit_true i rho e) =
  let aux (nu:value -> real) : Lemma
      (requires E.numeric_model i nu) (ensures lit_true i rho e) =
    lemma_triangle_equality e i nu rho
  in
  FStar.Classical.exists_elim (lit_true i rho e)
    #(value -> real) #(fun nu -> E.numeric_model i nu) () (fun nu -> aux nu)
