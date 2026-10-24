module Z3LpGomory

open FStar.Real
open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open Z3ProofIndex
open FStar.List.Tot
module A = Z3LinearArithmeticAst
module E = Z3LinearArithmeticEmbed
module P = Z3LinearArithmeticTheory
module C = Z3LpCertificate
module I = Z3IntegerRewrite
module L = FStar.List.Tot

type certificate = {
  split: expr;
  threshold: int;
  below: list A.coefficient;
  above: list A.coefficient;
}

let integer (n:int) : expr =
  App { decl_name = "lp-integer"; domain = []; range = A.int_s;
        interp = Some op_num_rational; int_params = [n; 1] } []

let arithmetic (name:string) (op:decl_kind) (a b:expr) : expr =
  App { decl_name = name; domain = [A.int_s; A.int_s]; range = A.int_s;
        interp = Some op; int_params = [] } [a; b]

let add (a b:expr) : expr = arithmetic "+" op_arith_add a b
let subtract (a b:expr) : expr = arithmetic "-" op_arith_sub a b
let multiply (n:int) (e:expr) : expr = arithmetic "*" op_arith_mul (integer n) e

let branch (upper:bool) (c:certificate) : expr =
  let rhs = integer (if upper then c.threshold + 1 else c.threshold) in
  App { decl_name = if upper then ">=" else "<=";
        domain = [A.int_s; A.int_s]; range = bool_sort;
        interp = Some (if upper then op_arith_ge else op_arith_le);
        int_params = [] } [c.split; rhs]

let check (c:certificate) (conclusion:expr) (facts:list expr) : bool =
  get_sort c.split = A.int_s &&
  A.check c.below conclusion (facts @ [branch false c]) &&
  A.check c.above conclusion (facts @ [branch true c])

let rec lemma_conj_branch (i:interpretation value) (rho:env value) (facts:list expr) (e:expr)
  : Lemma (requires conj_holds i rho facts /\ lit_true i rho e)
          (ensures conj_holds i rho (facts @ [e]))
          (decreases facts) =
  match facts with
  | [] -> ()
  | _ :: rest -> lemma_conj_branch i rho rest e

let lemma_integer (i:interpretation value) (nu:value -> real) (rho:env value) (n:int)
  : Lemma (requires E.numeric_operators i nu)
          (ensures nu (eval i (integer n) rho) == of_int n) =
  E.lemma_linearize 1 (integer n) (P.constant n 1) i nu rho

let lemma_inequality (i:interpretation value) (nu:value -> real) (rho:env value)
                     (e a b:expr) (r:A.relation)
  : Lemma (requires E.numeric_operators i nu /\ A.comparison e == Some (r,a,b) /\ r <> A.Eq)
          (ensures lit_true i rho e <==>
             E.numeric_relation r (nu (eval i a rho)) (nu (eval i b rho))) =
  match e with App _ [_;_] -> () | _ -> ()

let lemma_split (c:certificate) (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ get_sort c.split = A.int_s)
          (ensures lit_true i rho (branch false c) \/ lit_true i rho (branch true c)) =
  assert (E.numeric_operators i nu);
  assert (VInt? (eval i c.split rho));
  let n = E.integer_value (eval i c.split rho) in
  assert (nu (eval i c.split rho) == of_int n);
  lemma_integer i nu rho c.threshold;
  lemma_integer i nu rho (c.threshold + 1);
  assert (A.comparison (branch false c) == Some (A.Le, c.split, integer c.threshold));
  assert (A.comparison (branch true c) == Some (A.Ge, c.split, integer (c.threshold + 1)));
  lemma_inequality i nu rho (branch false c) c.split (integer c.threshold) A.Le;
  lemma_inequality i nu rho (branch true c) c.split (integer (c.threshold + 1)) A.Ge;
  if n <= c.threshold then (
    assert (of_int n <=. of_int c.threshold);
    assert (lit_true i rho (branch false c)))
  else (
    assert (of_int (c.threshold + 1) <=. of_int n);
    assert (lit_true i rho (branch true c)))

let lemma_check_sound (c:certificate) (conclusion:expr) (facts:list expr)
                      (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    check c conclusion facts /\ conj_holds i rho facts)
          (ensures lit_true i rho conclusion) =
  let split (nu:value -> real)
    : Lemma (requires E.numeric_model i nu)
            (ensures lit_true i rho (branch false c) \/ lit_true i rho (branch true c))
    = lemma_split c i nu rho in
  FStar.Classical.exists_elim
    (lit_true i rho (branch false c) \/ lit_true i rho (branch true c))
    #(value -> real) #(fun nu -> E.numeric_model i nu) () (fun nu -> split nu);
  FStar.Classical.or_elim #(lit_true i rho (branch false c)) #(lit_true i rho (branch true c))
    #(fun () -> lit_true i rho conclusion)
    (fun _ ->
      lemma_conj_branch i rho facts (branch false c);
      E.lemma_check_with_numeric_model c.below conclusion (facts @ [branch false c]) i rho)
    (fun _ ->
      lemma_conj_branch i rho facts (branch true c);
      E.lemma_check_with_numeric_model c.above conclusion (facts @ [branch true c]) i rho)

let split_candidate (split:expr) (threshold:int) (conclusion:expr) (facts:list expr)
  : option certificate =
  let c = { split = split; threshold = threshold; below = []; above = [] } in
  A.synthesize conclusion (facts @ [branch false c]) >>= (fun below ->
  A.synthesize conclusion (facts @ [branch true c]) >>= (fun above ->
  let result = { c with below = below; above = above } in
  if check result conclusion facts then Some result else None))

let rec split_thresholds (split x:expr) (p:int) (rows:list A.poly)
                         (conclusion:expr) (facts:list expr)
  : Tot (option certificate) (decreases rows) =
  match rows with
  | [] -> None
  | row :: rest ->
    let a = A.search_coefficient x row.mono in
    let candidate =
      if a > 0 then split_candidate split ((-p * row.cst) / a) conclusion facts
      else if a < 0 then split_candidate split ((p * row.cst) / (-a)) conclusion facts
      else None in
    (match candidate with Some c -> Some c
     | None -> split_thresholds split x p rest conclusion facts)

(* Continued fractions propose short integer normals. Intercepts only propose
   thresholds: both sides of every split are replayed against the actual facts. *)
let rec split_convergents (fuel:nat) (x y:expr) (sign:int)
                          (a b:nat) (p0 p1 q0 q1:int) (rows:list A.poly)
                          (conclusion:expr) (facts:list expr)
  : Tot (option certificate) (decreases fuel) =
  if fuel = 0 || b = 0 then None else
  let k = a / b in
  let p, q = k * p1 + p0, k * q1 + q0 in
  let split = add (multiply p x) (multiply (sign * q) y) in
  match split_thresholds split x p rows conclusion facts with
  | Some c -> Some c
  | None -> split_convergents (fuel - 1) x y sign b (a % b) p1 p q1 q
              rows conclusion facts

let rec split_terms (terms:list (int & expr)) : Tot (list (int & expr)) (decreases terms) =
  match terms with
  | [] -> []
  | (n, e) :: rest -> if n = 0 then split_terms rest else (n, e) :: split_terms rest

let rec split_inputs (facts:list expr) : Tot (option (list A.poly)) (decreases facts) =
  match facts with
  | [] -> Some []
  | e :: rest ->
    A.prepare_literal (1, 1) true e >>= (fun p ->
    split_inputs rest >>= (fun rows ->
    Some ({ p.poly with mono = split_terms (P.collect p.poly.mono []) } :: rows)))

let rec split_normals (candidates rows:list A.poly) (conclusion:expr) (facts:list expr)
  : Tot (option certificate) (decreases candidates) =
  match candidates with
  | [] -> None
  | row :: rest ->
    let candidate =
      match row.mono with
      | [(a, x); (b, y)] ->
        if get_sort x <> A.int_s || get_sort y <> A.int_s then None
        else split_convergents 16 x y (if (a < 0) = (b < 0) then 1 else -1)
               (I.absolute a) (I.absolute b) 0 1 1 0 rows conclusion facts
      | _ -> None in
    (match candidate with Some c -> Some c
     | None -> split_normals rest rows conclusion facts)

let synthesize_split (conclusion:expr) (facts:list expr) : option certificate =
  if conclusion <> false_expr || length facts > 8 then None else
  split_inputs facts >>= (fun rows -> split_normals rows rows conclusion facts)

let inferred_split (conclusion:expr) (facts:list expr) : bool =
  match synthesize_split conclusion facts with
  | Some c -> check c conclusion facts
  | None -> false

let lemma_inferred_split_sound (conclusion:expr) (facts:list expr)
                               (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    inferred_split conclusion facts /\ conj_holds i rho facts)
          (ensures lit_true i rho conclusion) =
  match synthesize_split conclusion facts with
  | Some c -> lemma_check_sound c conclusion facts i rho
  | None -> ()

type rational = C.rational
let zero : rational = 0, 1
let one : rational = 1, 1
let neg ((n,d):rational) : rational = -n,d
let plus ((n,d):rational) ((m,e):rational) : rational = n*e+m*d,d*e
let minus (a b:rational) : rational = plus a (neg b)
let times ((n,d):rational) ((m,e):rational) : rational = n*m,d*e
let divide ((n,d):rational) ((m,e):rational) : option rational =
  if m > 0 then Some (n*e,d*m)
  else if m < 0 then Some (-n*e,d*(-m)) else None
let equal ((n,d):rational) ((m,e):rational) : bool = n*e=m*d
let positive ((n,_):rational) : bool = n>0
let less ((n,d):rational) ((m,e):rational) : bool = n*e<m*d
let floor ((n,d):rational) : int = n/d
let fraction ((n,d):rational) : rational = n%d,d

let lcm (a b:pos) : option pos =
  let g = I.gcd a b in
  if g > 0 then let result = (a/g)*b in
    if result > 0 then Some result else None
  else None

let rec denominator_scale (scale:pos) (terms:C.polynomial)
  : Tot (option pos) (decreases terms) =
  match terms with
  | [] -> Some scale
  | ((_,d),_) :: rest ->
    lcm scale d >>= (fun next -> denominator_scale next rest)

let fact_scale (variables:list C.variable) (f:C.fact) : option pos =
  if L.for_all (fun (term:rational & nat) ->
      match C.lookup variables (snd term) with
      | Some v -> get_sort v.term = A.int_s | None -> false) f.lhs
  then denominator_scale (snd f.rhs) f.lhs else Some 1

let bound_fact (context:C.certificate) (s:C.step) (index:nat) (lower:bool) : option C.fact =
  C.lookup s.premises index >>= (fun (j,weight) ->
  C.lookup context.steps j >>= (fun f ->
  if equal weight one && not f.conclusion.contradiction &&
     equal f.conclusion.epsilon zero &&
     (f.conclusion.relation = C.Eq ||
      (if lower then f.conclusion.relation = C.Ge || f.conclusion.relation = C.Gt
       else f.conclusion.relation = C.Le || f.conclusion.relation = C.Lt))
  then Some f.conclusion else None))

type column =
  | Integral : coefficient:int -> term:expr -> column
  | Fixed : coefficient:rational -> shift:rational -> lower:nat -> upper:nat -> column
  | Shifted : coefficient:rational -> term:expr -> integer:bool ->
              shift:rational -> lower:bool -> index:nat -> column

let rec find_bounds (column:nat) (found:option C.column_bounds) (bounds:list C.column_bounds)
  : Tot (option (option C.column_bounds)) (decreases bounds) =
  match bounds with
  | [] -> Some found
  | b :: rest ->
    if b.bound_column <> column then find_bounds column found rest
    else if Some? found then None else find_bounds column (Some b) rest

let column_of (context:C.certificate) (s:C.step) (coefficient:rational) (j:nat)
  : option column =
  C.lookup context.variables j >>= (fun v ->
  find_bounds j None s.bounds >>= (fun bounds ->
  let lower,upper = match bounds with Some b -> b.lower,b.upper | None -> None,None in
  match lower,upper with
  | Some lo,Some hi ->
    bound_fact context s lo true >>= (fun l ->
    bound_fact context s hi false >>= (fun h ->
    if equal l.rhs h.rhs && l.relation <> C.Gt && h.relation <> C.Lt
    then Some (Fixed coefficient l.rhs lo hi) else None))
  | _,_ ->
    if v.integer && fst coefficient % snd coefficient = 0
    then Some (Integral (floor coefficient) v.term)
    else
      (match lower,upper with
       | Some index,None | None,Some index ->
         bound_fact context s index (Some? lower) >>= (fun f ->
         if v.integer && fst f.rhs % snd f.rhs <> 0 then None
         else Some (Shifted coefficient v.term v.integer f.rhs (Some? lower) index))
       | _,_ -> None)))

let rec columns_of (context:C.certificate) (s:C.step) (pivot:nat)
                   (seen:list nat) (row:C.polynomial)
  : Tot (option (list column)) (decreases row) =
  match row with
  | [] -> Some []
  | (coefficient,j) :: rest ->
    if L.mem j seen then None else
    let next () = columns_of context s pivot (j::seen) rest in
    if j = pivot then (if equal coefficient one then next () else None)
    else if equal coefficient zero then next ()
    else column_of context s coefficient j >>= (fun c ->
      next () >>= (fun cs -> Some (c::cs)))

let rec offset (columns:list column) : Tot rational (decreases columns) =
  match columns with
  | [] -> zero
  | Integral _ _ :: rest -> offset rest
  | Fixed c shift _ _ :: rest | Shifted c _ _ shift _ _ :: rest ->
    minus (offset rest) (times c shift)

let rec add_weight (index:nat) (weight:rational) (weights:list rational)
  : Tot (option (list rational)) (decreases weights) =
  match weights with
  | [] -> None
  | w::rest ->
    if index = 0 then Some (plus w weight::rest)
    else add_weight (index-1) weight rest >>= (fun tail -> Some (w::tail))

let add_bound (context:C.certificate) (s:C.step) (lower:bool)
              (index:nat) (weight:rational) (weights:list rational)
  : option (list rational) =
  bound_fact context s index lower >>= (fun f ->
  fact_scale context.variables f >>= (fun scale ->
  let weight = if lower && f.relation = C.Eq then neg weight else weight in
  add_weight index (times weight (1,scale)) weights))

let rec candidates (context:C.certificate) (s:C.step) (f:rational)
                   (columns:list column) (split:expr) (below above:list rational)
  : Tot (option (expr & list rational & list rational)) (decreases columns) =
  match columns with
  | [] -> Some (split,below,above)
  | Integral n term :: rest ->
    candidates context s f rest (add split (multiply n term)) below above
  | Fixed c _ lo hi :: rest ->
    let nonnegative = fst c >= 0 in
    let magnitude = if nonnegative then c else neg c in
    add_bound context s (not nonnegative) (if nonnegative then hi else lo) magnitude below >>= (fun below ->
    add_bound context s nonnegative (if nonnegative then lo else hi) magnitude above >>= (fun above ->
    candidates context s f rest split below above))
  | Shifted c term integral shift lower index :: rest ->
    let direction = if lower then neg c else c in
    let q = if integral then floor direction +
              (if less (minus one f) (fraction direction) then 1 else 0) else 0 in
    let h = minus direction (q,1) in
    let denominator = if fst h >= 0 then minus one f else f in
    divide (if fst h >= 0 then h else neg h) denominator >>= (fun weight ->
    let below_weight = plus h (times f weight) in
    let above_weight = minus (times (minus one f) weight) h in
    if fst below_weight < 0 || fst above_weight < 0 then None else
    let split =
      if integral then
        let z = if lower then subtract term (integer (floor shift))
                else subtract (integer (floor shift)) term in
        subtract split (multiply q z)
      else split in
    add_bound context s lower index below_weight below >>= (fun below ->
    add_bound context s lower index above_weight above >>= (fun above ->
    candidates context s f rest split below above)))

(* The context suggests a split and weights; only check on the actual
   premise/conclusion ASTs establishes the cut, not these metadata. *)
let candidate (context:C.certificate) (index:nat) : option certificate =
  C.lookup context.steps index >>= (fun s ->
  s.pivot >>= (fun pivot ->
  C.lookup context.variables pivot >>= (fun v ->
  if s.rule <> C.Gomory || not v.integer || get_sort v.term <> A.int_s ||
     s.equation.relation <> C.Eq || s.equation.contradiction ||
     not (equal s.equation.rhs zero && equal s.equation.epsilon zero) ||
     s.conclusion.contradiction || s.conclusion.relation <> C.Ge ||
     not (L.mem pivot (L.map (fun (term:rational & nat) -> snd term) s.equation.lhs))
  then None else
  columns_of context s pivot [] s.equation.lhs >>= (fun columns ->
  let k = offset columns in
  let f = fraction k in
  if not (positive f && less f one) then None else
  let weights = L.map (fun _ -> zero) s.premises in
  candidates context s f columns v.term weights weights >>= (fun (split,below,above) ->
  fact_scale context.variables s.conclusion >>= (fun scale ->
  Some { split = split; threshold = floor k;
         below = zero :: (below @ [one; times f (1,scale)]);
         above = zero :: (above @ [one; times (minus one f) (1,scale)]) }))))))
