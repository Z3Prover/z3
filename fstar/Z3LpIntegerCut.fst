module Z3LpIntegerCut

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open FStar.Real
open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open FStar.List.Tot
module A = Z3LinearArithmeticAst
module E = Z3LinearArithmeticEmbed
module P = Z3LinearArithmeticTheory
module G = Z3LpGomory
module I = Z3IntegerRewrite
module L = FStar.List.Tot

(* Integer rounding (Chvatal-Gomory) cuts for refutations over integer atoms.

   A certificate is a list of rounded bounds and a final refutation.
   Every bound is justified by `Z3LinearArithmeticAst.check` from the premises
   and the bounds before it: one weight per premise or earlier bound, then the
   weight of the negated bound. That check rounds a strict inequality over
   Int-sorted terms to a non-strict one (a < b gives a + 1 <= b), which is what
   makes a bound such as `x <= floor (c / g)` a consequence of `g * x <= c`.
   Nothing here is trusted: neither the bounds, their weights, nor the search
   that proposes them. The conclusion is derived only if every replay succeeds. *)

type step = {
  bound: expr;
  weights: list A.coefficient;
}

type certificate = {
  steps: list step;
  refutation: list A.coefficient;
}

let rec check_steps (steps:list step) (facts:list expr) : Tot bool (decreases steps) =
  match steps with
  | [] -> true
  | s :: rest -> A.check s.weights s.bound facts && check_steps rest (facts @ [s.bound])

let rec accumulated (steps:list step) (facts:list expr) : Tot (list expr) (decreases steps) =
  match steps with
  | [] -> facts
  | s :: rest -> accumulated rest (facts @ [s.bound])

let check (c:certificate) (conclusion:expr) (facts:list expr) : bool =
  check_steps c.steps facts && A.check c.refutation conclusion (accumulated c.steps facts)

let rec lemma_steps_sound (steps:list step) (facts:list expr)
                          (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    check_steps steps facts /\ conj_holds i rho facts)
          (ensures conj_holds i rho (accumulated steps facts))
          (decreases steps) =
  match steps with
  | [] -> ()
  | s :: rest ->
    E.lemma_check_with_numeric_model s.weights s.bound facts i rho;
    G.lemma_conj_branch i rho facts s.bound;
    lemma_steps_sound rest (facts @ [s.bound]) i rho

let lemma_check_sound (c:certificate) (conclusion:expr) (facts:list expr)
                      (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    check c conclusion facts /\ conj_holds i rho facts)
          (ensures lit_true i rho conclusion) =
  lemma_steps_sound c.steps facts i rho;
  E.lemma_check_with_numeric_model c.refutation conclusion (accumulated c.steps facts) i rho

(* Untrusted candidate generation. A row stands for `poly <= 0` and records, as
   `search_weights`, how it combines the premises. *)

(* Every cap fails closed: the search returns no certificate and the step stays an
   obligation. Rows, weights and constants are bounded before any combination, and the
   work counter bounds the pairs formed across all eliminations. *)
let max_premises : nat = 32
let max_rows : nat = 128
let max_cuts : nat = 8
let max_terms : nat = 64
let max_work : nat = 4096
let max_magnitude : int = 340282366920938463463374607431768211456

let rec small (rows:list A.search_row) : Tot bool (decreases rows) =
  match rows with
  | [] -> true
  | r :: rest ->
    let tiny (n:int) : bool = n <= max_magnitude && n >= -max_magnitude in
    tiny r.search_poly.cst && r.search_poly.denom <= max_magnitude &&
    L.for_all (fun (t:int & expr) -> tiny (fst t)) r.search_poly.mono &&
    L.for_all tiny r.search_weights && small rest

let at_most (lhs:expr) (k:int) : expr =
  App { decl_name = "<="; domain = [A.int_s; A.int_s]; range = bool_sort;
        interp = Some op_arith_le; int_params = [] } [lhs; G.integer k]

let rec nonzero_terms (ms:list (int & expr)) : Tot (list (int & expr)) (decreases ms) =
  match ms with
  | [] -> []
  | (n, e) :: rest -> if n = 0 then nonzero_terms rest else (n, e) :: nonzero_terms rest

let rec integer_terms (ms:list (int & expr)) : Tot bool (decreases ms) =
  match ms with
  | [] -> true
  | (_, e) :: rest -> get_sort e = A.int_s && integer_terms rest

let rec sum_terms (ms:list (int & expr)) : Tot expr (decreases ms) =
  match ms with
  | [] -> G.integer 0
  | [(n, e)] -> G.multiply n e
  | (n, e) :: rest -> G.add (G.multiply n e) (sum_terms rest)

let rec divide_terms (d:pos) (ms:list (int & expr)) : Tot (list (int & expr)) (decreases ms) =
  match ms with
  | [] -> []
  | (n, e) :: rest -> (n / d, e) :: divide_terms d rest

let rec zero_weights (k:nat) : Tot (list int) (decreases k) =
  if k = 0 then [] else 0 :: zero_weights (k - 1)

let rec zeros (k:nat) : Tot (list A.coefficient) (decreases k) =
  if k = 0 then [] else (let z:A.coefficient = 0, 1 in z) :: zeros (k - 1)

let rec as_coefficients (ws:list int) : Tot (list A.coefficient) (decreases ws) =
  match ws with
  | [] -> []
  | w :: rest -> (let c:A.coefficient = w, 1 in c) :: as_coefficients rest

let rec negated_terms (ms ns:list (int & expr)) : Tot bool (decreases ms) =
  match ms with
  | [] -> true
  | (c, e) :: rest -> A.search_coefficient e ns = -c && negated_terms rest ns

let rec same_terms (ms ns:list (int & expr)) : Tot bool (decreases ms) =
  match ms with
  | [] -> true
  | (c, e) :: rest -> A.search_coefficient e ns = c && same_terms rest ns

(* The two halves of an equality: `p + c <= 0` and `-p - c <= 0`. *)
let opposite (r q:A.search_row) : bool =
  not r.search_strict && not q.search_strict &&
  r.search_poly.cst + q.search_poly.cst = 0 &&
  negated_terms r.search_poly.mono q.search_poly.mono &&
  negated_terms q.search_poly.mono r.search_poly.mono

let rec unit_atom (ms:list (int & expr)) : Tot (option expr) (decreases ms) =
  match ms with
  | [] -> None
  | (c, e) :: rest -> if c = 1 || c = -1 then Some e else unit_atom rest

let rec find_opposite (r:A.search_row) (rows:list A.search_row)
  : Tot (option A.search_row) (decreases rows) =
  match rows with
  | [] -> None
  | q :: rest -> if opposite r q then Some q else find_opposite r rest

let rec find_equality (rows:list A.search_row)
  : Tot (option (A.search_row & A.search_row & expr)) (decreases rows) =
  match rows with
  | [] -> None
  | r :: rest ->
    (match unit_atom r.search_poly.mono with
     | None -> find_equality rest
     | Some e ->
       (match find_opposite r rest with
        | Some q -> Some (r, q, e)
        | None -> find_equality rest))

let rec remove_row (x:A.search_row) (rows:list A.search_row)
  : Tot (list A.search_row) (decreases rows) =
  match rows with
  | [] -> []
  | y :: rest -> if y = x then rest else y :: remove_row x rest

(* Eliminate the atom e from a row using the equality halves r (coefficient of e
   is positive) and q (negative). Only non-negative multiples are added. *)
let eliminate_atom (e:expr) (positive negative:A.search_row) (s:A.search_row)
  : option A.search_row =
  let b = A.search_coefficient e s.search_poly.mono in
  if b > 0 then A.search_add 1 s b negative
  else if b < 0 then A.search_add 1 s (-b) positive
  else Some s

let rec eliminate_in (e:expr) (positive negative:A.search_row) (rows:list A.search_row)
  : Tot (option (list A.search_row)) (decreases rows) =
  match rows with
  | [] -> Some []
  | s :: rest ->
    (match eliminate_atom e positive negative s, eliminate_in e positive negative rest with
     | Some s', Some rest' -> Some (s' :: rest')
     | _, _ -> None)

(* Substitute away every unit-coefficient equality. Substitution stops, keeping the
   rows so far, as soon as a coefficient would exceed the magnitude cap. *)
let rec eliminate_equalities (fuel:nat) (rows:list A.search_row)
  : Tot (list A.search_row) (decreases fuel) =
  if fuel = 0 then rows
  else match find_equality rows with
  | None -> rows
  | Some (r, q, e) ->
    let rest = remove_row q (remove_row r rows) in
    let positive, negative =
      if A.search_coefficient e r.search_poly.mono > 0 then r, q else q, r in
    (match eliminate_in e positive negative rest with
     | Some rows' -> if small rows' then eliminate_equalities (fuel - 1) rows' else rows
     | None -> rows)

type rounded = {
  scaled: list (int & expr);
  upper: int;
  derivation: list int;
  divisor: pos;
}

(* g * L + c <= 0 over integer atoms with g | the coefficients of the row but
   g not dividing c gives L <= floor (-c / g). *)
let round_row (s:A.search_row) : option rounded =
  let ms = nonzero_terms s.search_poly.mono in
  let g = I.divisor ms in
  if s.search_strict || s.search_poly.denom <> 1 || g < 2 || length ms > max_terms ||
     not (integer_terms ms) || s.search_poly.cst % g = 0
  then None
  else Some { scaled = divide_terms g ms; upper = (-s.search_poly.cst) / g;
              derivation = s.search_weights; divisor = g }

let rec mem_rounded (r:rounded) (rs:list rounded) : Tot bool (decreases rs) =
  match rs with
  | [] -> false
  | q :: rest -> (same_terms r.scaled q.scaled && same_terms q.scaled r.scaled && r.upper = q.upper) ||
                 mem_rounded r rest

let rec round_rows (rows:list A.search_row) (found:list rounded)
  : Tot (list rounded) (decreases rows) =
  match rows with
  | [] -> found
  | s :: rest ->
    (match round_row s with
     | Some r -> if mem_rounded r found || length found >= max_cuts then round_rows rest found
                 else round_rows rest (found @ [r])
     | None -> round_rows rest found)

let rec steps_of (j:nat) (rs:list rounded) : Tot (list step) (decreases rs) =
  match rs with
  | [] -> []
  | r :: rest ->
    { bound = at_most (sum_terms r.scaled) r.upper;
      weights = as_coefficients r.derivation @ zeros j @ [(let c:A.coefficient = r.divisor, 1 in c)] }
    :: steps_of (j + 1) rest

let rec bound_rows (n size j:nat) (rs:list rounded) : Tot (list A.search_row) (decreases rs) =
  match rs with
  | [] -> []
  | r :: rest ->
    { A.search_poly = { P.mono = r.scaled; P.cst = -r.upper; P.denom = 1 };
      A.search_weights = A.search_basis (n + j) size 1;
      A.search_strict = false } :: bound_rows n size (j + 1) rest

let rec extend_rows (k:nat) (rows:list A.search_row) : Tot (list A.search_row) (decreases rows) =
  match rows with
  | [] -> []
  | r :: rest ->
    { r with A.search_weights = r.search_weights @ zero_weights k } :: extend_rows k rest

(* Fourier-Motzkin elimination with the cheapest atom first; an atom that occurs
   with only one sign drops its rows. *)
let rec occurrence (e:expr) (rows:list A.search_row) : Tot (nat & nat) (decreases rows) =
  match rows with
  | [] -> 0, 0
  | r :: rest ->
    let p, n = occurrence e rest in
    let c = A.search_coefficient e r.search_poly.mono in
    if c > 0 then p + 1, n else if c < 0 then p, n + 1 else p, n

let rec cheapest_among (rows:list A.search_row) (es:list expr) (best:option (expr & nat))
  : Tot (option (expr & nat)) (decreases es) =
  match es with
  | [] -> best
  | e :: rest ->
    let p, n = occurrence e rows in
    let cost = p * n in
    if p + n = 0 then cheapest_among rows rest best
    else (match best with
          | Some (_, c) -> if cost < c then cheapest_among rows rest (Some (e, cost))
                           else cheapest_among rows rest best
          | None -> cheapest_among rows rest (Some (e, cost)))

let rec atoms_of (rows:list A.search_row) : Tot (list expr) (decreases rows) =
  match rows with
  | [] -> []
  | r :: rest ->
    let tail = atoms_of rest in
    L.fold_left (fun (acc:list expr) (t:int & expr) ->
        if fst t <> 0 && not (L.mem (snd t) acc) then snd t :: acc else acc)
      tail r.search_poly.mono

let cheapest (rows:list A.search_row) : option expr =
  match cheapest_among rows (atoms_of rows) None with
  | Some (e, _) -> Some e
  | None -> None

let dominates (q r:A.search_row) : bool =
  same_terms q.search_poly.mono r.search_poly.mono &&
  same_terms r.search_poly.mono q.search_poly.mono &&
  q.search_poly.cst >= r.search_poly.cst && (q.search_strict || not r.search_strict)

let rec dominated (r:A.search_row) (kept:list A.search_row) : Tot bool (decreases kept) =
  match kept with
  | [] -> false
  | q :: rest -> dominates q r || dominated r rest

let rec drop_dominated (r:A.search_row) (kept:list A.search_row)
  : Tot (list A.search_row) (decreases kept) =
  match kept with
  | [] -> []
  | q :: rest -> if dominates r q then drop_dominated r rest else q :: drop_dominated r rest

let insert_row (r:A.search_row) (kept:list A.search_row) : list A.search_row =
  if dominated r kept then kept else r :: drop_dominated r kept

let rec prune (rows kept:list A.search_row) : Tot (list A.search_row) (decreases rows) =
  match rows with
  | [] -> kept
  | r :: rest -> prune rest (insert_row r kept)

let rec refute_rows (fuel work:nat) (rows:list A.search_row)
  : Tot (option (list A.coefficient)) (decreases fuel) =
  match A.search_contradiction rows with
  | Some weights -> Some weights
  | None ->
    if fuel = 0 || length rows > max_rows then None
    else match cheapest rows with
    | None -> None
    | Some e ->
      let positive, negative, zero = A.search_partition e rows in
      let pairs = length positive * length negative in
      if pairs > work || pairs + length zero > max_rows then None else
      (match A.search_pairs (max_rows - length zero) e positive negative with
       | Some produced ->
         let next = prune (zero @ produced) [] in
         if small next then refute_rows (fuel - 1) (work - pairs) next else None
       | None -> None)

let synthesize (conclusion:expr) (facts:list expr) : option certificate =
  if conclusion <> false_expr || length facts > max_premises then None
  else
    let n = length facts in
    let rows = A.search_inputs n 0 (A.assumptions conclusion facts) in
    if not (small rows) then None
    else
      let rounded = round_rows (eliminate_equalities (length rows) rows) [] in
      let k = length rounded in
      let size = n + k in
      (match refute_rows 64 max_work (prune (extend_rows k rows @ bound_rows n size 0 rounded) []) with
       | Some refutation -> Some ({ steps = steps_of 0 rounded; refutation = refutation })
       | None -> None)

let inferred (conclusion:expr) (facts:list expr) : bool =
  match synthesize conclusion facts with
  | Some c -> check c conclusion facts
  | None -> false

let lemma_inferred_sound (conclusion:expr) (facts:list expr)
                         (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    inferred conclusion facts /\ conj_holds i rho facts)
          (ensures lit_true i rho conclusion) =
  match synthesize conclusion facts with
  | Some c -> lemma_check_sound c conclusion facts i rho
  | None -> ()
