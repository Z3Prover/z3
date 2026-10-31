module Z3OptNraFragment

(* Model of opt_nlsat.cpp nra_fragment_check / in_nra_fragment at head ee33f5d.
   A node abstracts one visited app: frag_ok = family/arity test passes,
   sort_kind = Bool | Real | Int | Other, is_num = a.is_numeral(n). *)
type sk = | Bool | Real | Int | Other
type node = { frag_ok: bool; sk: sk; is_num: bool }
type st = { ok: bool; has_int: bool }

let step (s:st) (n:node) : st =
  if not s.ok then s
  else
    let ok1 = n.frag_ok in
    if n.sk = Other then { ok = false; has_int = s.has_int }
    else if n.sk = Int && not n.is_num then { ok = ok1; has_int = true }
    else { ok = ok1; has_int = s.has_int }

let rec scan (s:st) (l:list node) : Tot st (decreases l) =
  match l with [] -> s | n::r -> scan (step s n) r

let rec all_frag (l:list node) : bool =
  match l with [] -> true | n::r -> n.frag_ok && n.sk <> Other && all_frag r
let rec no_nonnum_int (l:list node) : bool =
  match l with [] -> true | n::r -> not (n.sk = Int && not n.is_num) && no_nonnum_int r

(* in_nra_fragment: scan each hard formula with early exit, then obj. *)
let rec hard_loop (reals_only:bool) (s:st) (hs:list (list node)) (obj:list node) : Tot bool (decreases hs) =
  match hs with
  | [] -> let s' = scan s obj in s'.ok && not (reals_only && s'.has_int)
  | f::r -> let s' = scan s f in
            if not s'.ok || (reals_only && s'.has_int) then false
            else hard_loop reals_only s' r obj

let rec flat (hs:list (list node)) (obj:list node) : Tot (list node) (decreases hs) =
  match hs with [] -> obj | f::r -> List.Tot.append f (flat r obj)

(* O1: ok is exactly the all-nodes-in-fragment predicate (unchanged semantics). *)
let rec scan_ok (s:st) (l:list node)
  : Lemma (ensures (scan s l).ok == (s.ok && all_frag l)) (decreases l) =
  match l with [] -> () | n::r -> scan_ok (step s n) r

(* O2: has_int tracks non-numeral Int nodes whenever the scan stays ok. *)
let rec scan_has (s:st) (l:list node)
  : Lemma (ensures (scan s l).ok ==> ((scan s l).has_int == (s.has_int || not (no_nonnum_int l))))
          (decreases l) =
  match l with [] -> () | n::r -> (scan_has (step s n) r; scan_ok s l; scan_ok (step s n) r; assert_norm (scan s (n::r) == scan (step s n) r))

let rec scan_sticky (s:st) (l:list node)
  : Lemma (ensures s.has_int ==> (scan s l).has_int) (decreases l) =
  match l with [] -> () | n::r -> scan_sticky (step s n) r

let rec scan_app (s:st) (a b:list node)
  : Lemma (ensures scan s (List.Tot.append a b) == scan (scan s a) b) (decreases a) =
  match a with [] -> () | n::r -> scan_app (step s n) r b

(* O3: the early exits are sound: the loop result equals the single scan over all
   visited nodes; with reals_only=false this is the pre-PR behavior (ok only). *)
let rec loop_eq (ro:bool) (s:st) (hs:list (list node)) (obj:list node)
  : Lemma (ensures hard_loop ro s hs obj ==
            (let t = scan s (flat hs obj) in t.ok && not (ro && t.has_int)))
          (decreases hs) =
  match hs with
  | [] -> ()
  | f::r ->
    scan_app s f (flat r obj);
    let s' = scan s f in
    scan_sticky s' (flat r obj);
    scan_ok s' (flat r obj);
    (if s'.ok then loop_eq ro s' r obj else ());
    (if not s'.ok then (scan_ok s f; scan_ok s (flat hs obj)) else ())

let main_ok (ro:bool) (hs:list (list node)) (obj:list node)
  : Lemma (hard_loop ro ({ok=true; has_int=false}) hs obj
           == (all_frag (flat hs obj) && not (ro && not (no_nonnum_int (flat hs obj)))))
  = let s0 = {ok=true; has_int=false} in
    loop_eq ro s0 hs obj; scan_ok s0 (flat hs obj); scan_has s0 (flat hs obj)

(* reals_only=false: result is exactly all_frag, independent of Int terms. *)
let old_behavior (hs:list (list node)) (obj:list node)
  : Lemma (hard_loop false ({ok=true; has_int=false}) hs obj == all_frag (flat hs obj))
  = main_ok false hs obj
