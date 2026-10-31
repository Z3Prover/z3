module PulseMip.Certificate

open FStar.Real
open FStar.List.Tot
open PulseMip.Model
module L = FStar.List.Tot
module P = Z3LinearArithmeticTheory
module Q = PulseMip.Rational

#set-options "--z3rlimit 10 --smtencoding.nl_arith_repr native"

type tree =
  | Contradiction : weights:list nat -> tree
  | LowerBound : weights:list nat -> scale:pos -> tree
  | Split : variable:nat -> pivot:int -> left:tree -> right:tree -> tree

type reason = | NodeLimit | RowLimit
type result =
  | Optimal : solution:point -> certificate:tree -> result
  | Infeasible : certificate:tree -> result
  | Unbounded : solution:point -> direction:point -> result
  | Unknown : reason:reason -> incumbent:option point -> result
  | Error : message:string -> result

let rec weighted (ws:list nat) (rows:list polynomial)
  : Tot (option (p:polynomial{p.denom == 1})) (decreases rows) =
  match ws, rows with
  | [], [] -> Some P.zero
  | w :: wt, p :: rest ->
    if w < 0 then None else (match weighted wt rest with
     | None -> None
     | Some q -> Some (P.add (P.scale w 1 { p with denom = 1 }) q))
  | _, _ -> None

let cancelled (p c:polynomial) (s:pos) : bool =
  P.all_zero (P.collect (p.mono @ L.map (fun (a, v) -> (s * a, v)) c.mono) [])

let contradiction (ws:list nat) (rows:list polynomial) : bool =
  match weighted ws rows with
  | Some p -> P.all_zero (P.collect p.mono []) && p.cst > 0
  | None -> false

let bound (ws:list nat) (s:pos) (rows:list polynomial) (c:polynomial) (cut:Q.rational) : bool =
  s > 0 && cut.den > 0 && (match weighted ws rows with
  | Some p -> cancelled p c s && (p.cst + s * c.cst) * cut.den >= s * cut.num
  | None -> false)

let rec check_tree (integers:list nat) (rows:list polynomial) (c:polynomial)
                   (cut:option Q.rational) (t:tree) : Tot bool (decreases t) =
  match t with
  | Contradiction ws -> contradiction ws rows
  | LowerBound ws s -> (match cut with Some q -> bound ws s rows c q | None -> false)
  | Split v k left right ->
    v >= 0 && L.mem v integers &&
    check_tree integers (lower_branch v k :: rows) c cut left &&
    check_tree integers (upper_branch v k :: rows) c cut right

let homogeneous (p:polynomial) : polynomial = { p with cst = 0 }

let ray (p:problem) (d:point) : bool =
  point_valid d && L.length d = p.variables && integral_on p.integers d &&
  feasible_rows (L.map homogeneous p.constraints) d &&
  not (Q.le Q.zero (eval (homogeneous p.objective) d))

let accepts (p:problem) (r:result) : bool =
  valid p &&
  (match r with
   | Optimal x t -> feasible p x && check_tree p.integers p.constraints p.objective (Some (eval p.objective x)) t
   | Infeasible t -> check_tree p.integers p.constraints p.objective None t
   | Unbounded x d -> feasible p x && ray p d
   | Unknown _ None -> true
   | Unknown _ (Some x) -> feasible p x
   | Error _ -> true)

let certify (p:problem) (r:result) : r:result{accepts p r \/ Error? r} =
  if not (valid p) then Error "invalid problem: variable indices or polynomial denominators"
  else if accepts p r then r
  else Error "internal error: exact result certificate was rejected"

let rec lemma_weighted (ws:list nat) (rows:list polynomial) (p:polynomial{p.denom == 1}) (rho:nat -> real)
  : Lemma (requires rows_hold rows rho /\ weighted ws rows == Some p)
          (ensures P.value p rho <=. 0.0R) (decreases rows) =
  match ws, rows with
  | [], [] -> ()
  | w :: wt, a :: rest ->
    (match weighted wt rest with
     | None -> ()
     | Some q ->
       lemma_weighted wt rest q rho;
       P.lemma_scale w 1 { a with denom = 1 } rho;
       P.lemma_add (P.scale w 1 { a with denom = 1 }) q rho)
  | _, _ -> ()

let lemma_zero (p:polynomial) (rho:nat -> real)
  : Lemma (requires P.all_zero (P.collect p.mono []))
          (ensures P.value p rho == of_int p.cst) =
  P.lemma_collect p.mono [] rho;
  P.lemma_all_zero (P.collect p.mono []) rho

let lemma_cancelled (p c:polynomial) (s:pos) (rho:nat -> real)
  : Lemma (requires cancelled p c s)
          (ensures P.value p rho +. of_int s *. P.value c rho == of_int (p.cst + s * c.cst)) =
  P.lemma_collect (p.mono @ L.map (fun (a, v) -> (s * a, v)) c.mono) [] rho;
  P.lemma_all_zero (P.collect (p.mono @ L.map (fun (a, v) -> (s * a, v)) c.mono) []) rho;
  P.lemma_append p.mono (L.map (fun (a, v) -> (s * a, v)) c.mono) rho;
  P.lemma_scale_monomials s c.mono rho;
  Q.lemma_int_product s c.cst;
  Q.lemma_int_sum p.cst (s * c.cst)

#push-options "--using_facts_from 'Prims FStar.Real' --fuel 0 --ifuel 0"

let lemma_bound_arithmetic (s d:pos) (b n:int) (pv cv:real)
  : Lemma (requires pv <=. 0.0R /\ pv +. of_int s *. cv == of_int b /\ b * d >= s * n)
          (ensures of_int n /. of_int d <=. cv) =
  Q.lemma_int_product b d;
  Q.lemma_int_product s n

let lemma_split_arithmetic (v:nat) (k n:int) (rho:nat -> real)
  : Lemma (requires rho v == of_int n)
          (ensures (n <= k ==> rho v +. of_int (-k) <=. 0.0R) /\
                   (n > k ==> (of_int (-1) *. rho v +. of_int (k + 1)) <=. 0.0R)) = ()

#pop-options

let lemma_contradiction (ws:list nat) (rows:list polynomial) (rho:nat -> real)
  : Lemma (requires contradiction ws rows /\ rows_hold rows rho) (ensures False) =
  match weighted ws rows with
  | None -> ()
  | Some p -> lemma_weighted ws rows p rho; lemma_zero p rho

let lemma_bound (ws:list nat) (s:pos) (rows:list polynomial) (c:polynomial)
                (cut:Q.rational) (rho:nat -> real)
  : Lemma (requires bound ws s rows c cut /\ rows_hold rows rho)
          (ensures Q.value cut <=. P.value c rho) =
  match weighted ws rows with
  | None -> ()
  | Some p ->
    lemma_weighted ws rows p rho;
    lemma_cancelled p c s rho;
    lemma_bound_arithmetic s cut.den (p.cst + s * c.cst) cut.num (P.value p rho) (P.value c rho)

let rec lemma_tree (integers:list nat) (rows:list polynomial) (c:polynomial)
                   (cut:option Q.rational) (t:tree) (rho:nat -> real) (ints:nat -> int)
  : Lemma (requires check_tree integers rows c cut t /\ rows_hold rows rho /\
                    (forall (v:nat). L.mem v integers ==> rho v == of_int (ints v)))
          (ensures (match cut with None -> False | Some q -> Q.value q <=. P.value c rho))
          (decreases t) =
  match t with
  | Contradiction ws -> lemma_contradiction ws rows rho
  | LowerBound ws s -> (match cut with Some q -> lemma_bound ws s rows c q rho | None -> ())
  | Split v k left right ->
    lemma_split_arithmetic v k (ints v) rho;
    if ints v <= k then lemma_tree integers (lower_branch v k :: rows) c cut left rho ints
    else lemma_tree integers (upper_branch v k :: rows) c cut right rho ints

let lemma_infeasible (p:problem) (t:tree) (rho:nat -> real) (ints:nat -> int)
  : Lemma (requires accepts p (Infeasible t) /\ mixed p rho ints) (ensures False) =
  lemma_tree p.integers p.constraints p.objective None t rho ints

let lemma_optimal (p:problem) (x:point) (t:tree) (rho:nat -> real) (ints:nat -> int)
  : Lemma (requires accepts p (Optimal x t) /\ mixed p rho ints)
          (ensures feasible p x /\ Q.value (eval p.objective x) <=. P.value p.objective rho) =
  lemma_tree p.integers p.constraints p.objective (Some (eval p.objective x)) t rho ints

let lemma_homogeneous_rows (rows:list polynomial) (d:point)
  : Lemma (requires feasible_rows (L.map homogeneous rows) d)
          (ensures rows_hold (L.map homogeneous rows) (valuation d)) =
  lemma_feasible_rows (L.map homogeneous rows) d

let lemma_unbounded_direction (p:problem) (x d:point)
  : Lemma (requires accepts p (Unbounded x d))
          (ensures feasible p x /\ integral_on p.integers d /\
                    rows_hold (L.map homogeneous p.constraints) (valuation d) /\
                    P.value (homogeneous p.objective) (valuation d) <. 0.0R) =
  lemma_homogeneous_rows p.constraints d;
  lemma_eval (homogeneous p.objective) d;
  Q.lemma_le Q.zero (eval (homogeneous p.objective) d)

let line (rho delta:nat -> real) (t:nat) : nat -> real =
  fun v -> rho v +. of_int t *. delta v

#push-options "--using_facts_from 'Prims FStar.Real' --fuel 0 --ifuel 0"

let lemma_line_step (a x y r s t:real)
  : Lemma (a *. (x +. t *. y) +. (r +. t *. s) ==
           (a *. x +. r) +. t *. (a *. y +. s)) = ()

#pop-options

let rec lemma_line_terms (ms:list (int & nat)) (rho delta:nat -> real) (t:nat)
  : Lemma (P.monomial_value ms (line rho delta t) ==
           P.monomial_value ms rho +. of_int t *. P.monomial_value ms delta)
          (decreases ms) =
  match ms with
  | [] -> ()
  | (a, v) :: rest ->
    lemma_line_terms rest rho delta t;
    lemma_line_step (of_int a) (rho v) (delta v)
      (P.monomial_value rest rho) (P.monomial_value rest delta) (of_int t)

let lemma_line_polynomial (p:polynomial) (rho delta:nat -> real) (t:nat)
  : Lemma (P.value p (line rho delta t) ==
           P.value p rho +. of_int t *. P.value (homogeneous p) delta) =
  lemma_line_terms p.mono rho delta t

let rec lemma_line_rows (rows:list polynomial) (rho delta:nat -> real) (t:nat)
  : Lemma (requires rows_hold rows rho /\ rows_hold (L.map homogeneous rows) delta)
          (ensures rows_hold rows (line rho delta t)) (decreases rows) =
  match rows with
  | [] -> ()
  | p :: rest ->
    lemma_line_polynomial p rho delta t;
    lemma_line_rows rest rho delta t

let lemma_unbounded (p:problem) (x d:point) (t:nat)
  : Lemma (requires accepts p (Unbounded x d))
          (ensures
            mixed p (line (valuation x) (valuation d) t)
              (fun v -> Q.floor (at x v) + t * Q.floor (at d v)) /\
            P.value p.objective (line (valuation x) (valuation d) t) ==
              P.value p.objective (valuation x) +.
              of_int t *. P.value (homogeneous p.objective) (valuation d) /\
            (t > 0 ==> P.value p.objective (line (valuation x) (valuation d) t) <.
                       P.value p.objective (valuation x))) =
  lemma_unbounded_direction p x d;
  lemma_feasible p x;
  lemma_line_rows p.constraints (valuation x) (valuation d) t;
  lemma_line_polynomial p.objective (valuation x) (valuation d) t;
  let each (v:nat)
    : Lemma (L.mem v p.integers ==>
      line (valuation x) (valuation d) t v ==
      of_int (Q.floor (at x v) + t * Q.floor (at d v))) =
    if L.mem v p.integers then (
      lemma_integral_on p.integers d v;
      Q.lemma_int_product t (Q.floor (at d v));
      Q.lemma_int_sum (Q.floor (at x v)) (t * Q.floor (at d v))) in
  FStar.Classical.forall_intro each
