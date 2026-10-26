module Z3Pr11348Audit

type result = | Ok : bool -> result | Err : result
let set_global_decls (has_manager g v:bool) : result =
  if v <> g then (if has_manager then Err else Ok v) else Ok g

let ob1a (hm g:bool) : Lemma (ensures set_global_decls hm g g == Ok g) = ()
let ob1b (g:bool) : Lemma (ensures set_global_decls true g (not g) == Err) = ()
let ob1c (g v:bool) : Lemma (ensures (match set_global_decls false g v with Ok r -> r == v | Err -> False)) = ()

type just = | Axiom | NoJust
let inject (proofs:bool) : just = if proofs then Axiom else NoJust
let ob2a (p:bool) : Lemma (requires p) (ensures inject p == Axiom) = ()
let ob2b (p:bool) : Lemma (requires not p) (ensures inject p == NoJust) = ()

let ob3a (x n:int) : Lemma (requires n + 1 > 0) (ensures x % (n+1) <= n /\ 0 <= x % (n+1)) = ()
let ob3b (x y:int) : Lemma (requires y > 0) (ensures x % y - y <= -1) = ()
let ob3c (x y:int) : Lemma (requires y <> 0) (ensures x - y * (x / y) == x % y /\ 0 <= x % y) = ()
