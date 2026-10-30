module Z3BvInvertibilityConcat

open Z3BvTheory
module U = FStar.UInt
module I = Z3BvInvertibility
module C = Z3BvInvertibilityConditions

type position = | High | Low

let apply (#n:pos) (#m:pos) (p:position) (s:bv m) (x:bv n) : bv (n + m) =
  match p with
  | High -> bv_concat x s
  | Low -> bv_concat s x

let condition (#n:pos) (#m:pos) (p:position) (r:I.relation)
  (s:bv m) (tx:bv n) (ts:bv m) : bool =
  match p with
  | High ->
    (match r with
    | I.Eq -> s = ts
    | I.Ne -> true
    | I.Ult -> tx <> 0 || s < ts
    | I.Ugt -> tx <> U.ones n || s > ts
    | I.Ule -> tx <> 0 || s <= ts
    | I.Uge -> tx <> U.ones n || s >= ts
    | I.Slt -> tx <> C.signed_min n || s < ts
    | I.Sgt -> tx <> C.signed_max n || s > ts
    | I.Sle -> tx <> C.signed_min n || s <= ts
    | I.Sge -> tx <> C.signed_max n || s >= ts)
  | Low ->
    (match r with
    | I.Eq -> s = ts
    | I.Ne -> true
    | I.Ult -> s <= ts && (s <> ts || tx <> 0)
    | I.Ugt -> s >= ts && (s <> ts || tx <> U.ones n)
    | I.Ule -> s <= ts
    | I.Uge -> s >= ts
    | I.Slt -> I.holds I.Sle s ts && (s <> ts || tx <> 0)
    | I.Sgt -> I.holds I.Sge s ts && (s <> ts || tx <> U.ones n)
    | I.Sle -> I.holds I.Sle s ts
    | I.Sge -> I.holds I.Sge s ts)

let witness (#n:pos) (p:position) (r:I.relation) (tx:bv n) : bv n =
  match r with
  | I.Eq -> tx
  | I.Ne -> I.target I.Ne tx
  | I.Ult | I.Ule -> 0
  | I.Ugt | I.Uge -> U.ones n
  | I.Slt | I.Sle -> if p = High then C.signed_min n else 0
  | I.Sgt | I.Sge -> if p = High then C.signed_max n else U.ones n

let variable_part (#n:pos) (#m:pos) (p:position) (t:bv (n + m)) : bv n =
  match p with
  | High -> bv_extract (n + m - 1) m t
  | Low -> bv_extract (n - 1) 0 t

let fixed_part (#n:pos) (#m:pos) (p:position) (t:bv (n + m)) : bv m =
  match p with
  | High -> bv_extract (m - 1) 0 t
  | Low -> bv_extract (n + m - 1) n t

let condition_value (#n:pos) (#m:pos) (p:position) (r:I.relation)
  (s:bv m) (t:bv (n + m)) : bool =
  condition p r s (variable_part #n #m p t) (fixed_part #n #m p t)
