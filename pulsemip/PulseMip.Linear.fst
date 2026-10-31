module PulseMip.Linear

open PulseMip.Model
open FStar.List.Tot
module L = FStar.List.Tot
module P = Z3LinearArithmeticTheory
module Q = PulseMip.Rational

type derived = { row:polynomial; weights:list nat }
type projection = { rows:list derived; layers:list (nat & list derived) }
type endpoint = { q:Q.rational; source:derived }
type interval = { lo:option endpoint; hi:option endpoint }
type relaxation =
  | Empty : weights:list nat -> relaxation
  | Finite : solution:point -> weights:list nat -> scale:pos -> relaxation
  | Infinite : solution:point -> direction:point -> relaxation
  | Limited
  | Failed : message:string -> relaxation

let rec filter (#a:Type0) (predicate:a -> Tot bool) (xs:list a) : Tot (list a) (decreases xs) =
  match xs with [] -> [] | x :: rest -> if predicate x then x :: filter predicate rest else filter predicate rest

let rec coefficient (v:nat) (ms:list (int & nat)) : Tot int (decreases ms) =
  match ms with [] -> 0 | (a, w) :: rest -> (if v = w then a else 0) + coefficient v rest

let compact (p:polynomial) : polynomial =
  { p with mono = filter (fun (a, _) -> a <> 0) (P.collect p.mono []) }

let positive_coefficient (v:nat) (p:polynomial) : nat =
  let a = coefficient v p.mono in if a > 0 then a else 0

let negative_coefficient (v:nat) (p:polynomial) : nat =
  let a = coefficient v p.mono in if a < 0 then -a else 0

let rec basis (n i:nat) : Tot (list nat) (decreases n) =
  if n = 0 then [] else (if i = 0 then 1 else 0) :: basis (n - 1) (if i = 0 then n else i - 1)

let rec annotate (rows:list polynomial) (n i:nat) : Tot (list derived) (decreases rows) =
  match rows with [] -> [] | p :: rest -> { row = compact p; weights = basis n i } :: annotate rest n (i + 1)

let rec add_weights (xs ys:list nat) : Tot (list nat) (decreases xs) =
  match xs, ys with
  | [], _ -> ys
  | _, [] -> xs
  | x :: xt, y :: yt -> (x + y) :: add_weights xt yt

let combination (a b:nat) (x y:derived) : derived = {
  row = compact (P.add (P.scale a 1 x.row) (P.scale b 1 y.row));
  weights = add_weights (L.map (fun (w:nat) -> (a * w <: nat)) x.weights)
                        (L.map (fun (w:nat) -> (b * w <: nat)) y.weights);
}

let rec pairs (v:nat) (positive negative:list derived) : Tot (list derived) (decreases positive) =
  match positive with
  | [] -> []
  | x :: rest ->
    L.map (fun y -> combination
      (if coefficient v y.row.mono < 0 then -coefficient v y.row.mono else 0)
      (if coefficient v x.row.mono > 0 then coefficient v x.row.mono else 0) x y) negative @
    pairs v rest negative

let eliminate_variable (limit v:nat) (rows:list derived) : option (list derived) =
  let positive = filter (fun p -> coefficient v p.row.mono > 0) rows in
  let negative = filter (fun p -> coefficient v p.row.mono < 0) rows in
  let independent = filter (fun p -> coefficient v p.row.mono = 0) rows in
  if L.length independent + L.length positive * L.length negative > limit then None
  else Some (independent @ pairs v positive negative)

let rec project (limit v remaining:nat) (rows:list derived) (layers:list (nat & list derived))
  : Tot (option projection) (decreases remaining) =
  if L.length rows > limit then None
  else if remaining = 0 then Some { rows = rows; layers = layers }
  else match eliminate_variable limit v rows with
  | None -> None
  | Some next -> project limit (v + 1) (remaining - 1) next ((v, rows) :: layers)

let tighter_lo (old:option endpoint) (candidate:endpoint) : option endpoint =
  match old with Some e -> if Q.le candidate.q e.q then old else Some candidate | None -> Some candidate
let tighter_hi (old:option endpoint) (candidate:endpoint) : option endpoint =
  match old with Some e -> if Q.le e.q candidate.q then old else Some candidate | None -> Some candidate

let rec bounds (v:nat) (rows:list derived) (x:point) (acc:interval) : Tot interval (decreases rows) =
  match rows with
  | [] -> acc
  | p :: rest ->
    let a = coefficient v p.row.mono in
    let tail = eval p.row (put x v Q.zero) in
    let next =
      if a < 0 then { acc with lo = tighter_lo acc.lo { q = Q.div_pos tail (-a); source = p } }
      else if a > 0 then { acc with hi = tighter_hi acc.hi { q = Q.div_pos (Q.neg tail) a; source = p } }
      else acc in
    bounds v rest x next

let choose (b:interval) : Q.rational =
  match b.lo, b.hi with Some e, _ -> e.q | _, Some e -> e.q | _, _ -> Q.zero

let rec restore (layers:list (nat & list derived)) (x:point) : Tot point (decreases layers) =
  match layers with
  | [] -> x
  | (v, rows) :: rest ->
    let b = bounds v rows x { lo = None; hi = None } in
    restore rest (put x v (choose b))

let rec zeros (n:nat) : Tot point (decreases n) =
  if n = 0 then [] else Q.zero :: zeros (n - 1)

let rec constant_conflict (rows:list derived) : Tot (option (list nat)) (decreases rows) =
  match rows with
  | [] -> None
  | p :: rest ->
    if P.all_zero p.row.mono && p.row.cst > 0 then Some p.weights else constant_conflict rest

let rec prefix (#a:Type0) (n:nat) (xs:list a) : Tot (list a) (decreases xs) =
  match xs with [] -> [] | x :: rest -> if n = 0 then [] else x :: prefix (n - 1) rest

type feasibility =
  | Witness : solution:point -> feasibility
  | Refutation : weights:list nat -> feasibility
  | Exhausted
  | InvalidProjection

let find_point (limit n:nat) (rows:list polynomial) : feasibility =
  match project limit 0 n (annotate rows (L.length rows) 0) [] with
  | None -> Exhausted
  | Some p ->
    (match constant_conflict p.rows with
     | Some ws -> Refutation ws
     | None ->
       let x = restore p.layers (zeros n) in
       if feasible_rows rows x then Witness x else InvalidProjection)

let rec common_denominator (x:point) : Tot pos (decreases x) =
  match x with [] -> 1 | q :: rest -> q.den * common_denominator rest

let integer_direction (d:point) : point =
  let scale = common_denominator d in
  L.map (fun (q:Q.rational) -> Q.integer (q.num * (scale / q.den))) d

let recession (limit:nat) (p:problem) : feasibility =
  let decrease = { p.objective with cst = 1 } in
  match find_point limit p.variables (decrease :: L.map (fun (r:polynomial) -> { r with cst = 0 }) p.constraints) with
  | Witness d -> Witness (integer_direction d)
  | r -> r

let minimize (limit:nat) (p:problem) (rows:list polynomial) : relaxation =
  let n = p.variables in
  let m = L.length rows in
  let equation = { p.objective with mono = p.objective.mono @ [(-1, n)] } in
  let opposite = P.scale (-1) 1 equation in
  let augmented = rows @ [equation; opposite] in
  match project limit 0 n (annotate augmented (m + 2) 0) [] with
  | None -> Limited
  | Some projection ->
    (match constant_conflict projection.rows with
     | Some ws -> Empty (prefix m ws)
     | None ->
       let initial = zeros (n + 1) in
       let b = bounds n projection.rows initial { lo = None; hi = None } in
       let conflict = match b.lo, b.hi with
         | Some lo, Some hi ->
           if not (Q.le lo.q hi.q) then
             Some (combination (negative_coefficient n lo.source.row)
               (positive_coefficient n hi.source.row) hi.source lo.source)
           else None
         | _, _ -> None in
       match conflict with
       | Some contradiction -> Empty (prefix m contradiction.weights)
       | None ->
         let x = prefix n (restore projection.layers (put initial n (choose b))) in
         if not (feasible_rows rows x) then Failed "LP reconstruction failed exact feasibility"
         else match b.lo with
         | Some lo ->
           let a = coefficient n lo.source.row.mono in
           if a < 0 then Finite x (prefix m lo.source.weights) (-a)
           else Failed "LP lower bound has invalid sign"
         | None ->
           (match recession limit { p with constraints = rows } with
            | Witness d -> Infinite x d
            | Exhausted -> Limited
            | _ -> Failed "unbounded LP has no certified recession direction"))
