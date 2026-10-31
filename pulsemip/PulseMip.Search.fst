module PulseMip.Search

open PulseMip.Model
module C = PulseMip.Certificate
module LP = PulseMip.Linear
module Q = PulseMip.Rational

type step =
  | Close : certificate:C.tree -> step
  | Offer : solution:point -> certificate:C.tree -> step
  | Fork : variable:nat -> pivot:int -> step
  | Escape : solution:point -> direction:point -> step
  | Stop : reason:C.reason -> step
  | Fail : message:string -> step

type outcome =
  | Closed : certificate:C.tree -> outcome
  | Open : reason:C.reason -> outcome
  | Infinite : solution:point -> direction:point -> outcome
  | Broken : message:string -> outcome

let rec fractional (vs:list nat) (x:point) : Tot (option nat) (decreases vs) =
  match vs with
  | [] -> None
  | v :: rest -> if Q.integral (at x v) then fractional rest x else Some v

let branch (p:problem) (x:point) : step =
  match fractional p.integers x with
  | Some v -> Fork v (Q.floor (at x v))
  | None -> Fail "nonintegral LP point has no branching variable"

[@@"opaque_to_smt"]
let improve (p:problem) (x:point) (old:option point) : option point =
  match old with
  | Some y -> if Q.le (eval p.objective y) (eval p.objective x) then old else Some x
  | None -> Some x

[@@"opaque_to_smt"]
let plan (limit:nat) (p:problem) (rows:list polynomial) (best:option point) : step =
  match LP.minimize limit p rows with
  | LP.Limited -> Stop C.RowLimit
  | LP.Failed message -> Fail message
  | LP.Empty ws ->
    if C.contradiction ws rows then Close (C.Contradiction ws)
    else Fail "LP infeasibility certificate rejected"
  | LP.Finite x ws s ->
    if not (C.bound ws s rows p.objective (eval p.objective x)) then Fail "LP optimality certificate rejected"
    else
      let certificate = C.LowerBound ws s in
      let prune = match best with
        | Some y -> Q.le (eval p.objective y) (eval p.objective x)
        | None -> false in
      if prune then Close certificate
      else if integral_on p.integers x then Offer x certificate
      else branch p x
  | LP.Infinite x d ->
    if integral_on p.integers x then
      if C.ray { p with constraints = rows } d then Escape x d
      else Fail "LP recession certificate rejected"
    else branch p x

let join (v:nat) (k:int) (left right:outcome) : outcome =
  match left, right with
  | Infinite x d, _ | _, Infinite x d -> Infinite x d
  | Broken s, _ | _, Broken s -> Broken s
  | Closed a, Closed b -> Closed (C.Split v k a b)
  | Open r, _ | _, Open r -> Open r

let finish (o:outcome) (best:option point) : C.result =
  match o with
  | Closed t -> (match best with Some x -> C.Optimal x t | None -> C.Infeasible t)
  | Infinite x d -> C.Unbounded x d
  | Open r -> C.Unknown r best
  | Broken s -> C.Error s
