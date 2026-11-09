module AndCoreLowerBound
open FStar.List.Tot

(* Model of the scan in arith_rewriter::mk_and_core. a = numeral of args[0],
   sel = numeral of the currently selected arg0, l = numerals b of later args
   matching (b <= y). Non-matching args go to rest and are not modelled. *)
let rec old_scan (a sel:int) (l:list int) : Tot int (decreases l) =
  match l with
  | [] -> sel
  | b::t -> if b > a then old_scan a b t else old_scan a sel t

let rec new_scan (a sel:int) (l:list int) : Tot int (decreases l) =
  match l with
  | [] -> sel
  | b::t -> if b > a then new_scan b b t else new_scan a sel t

let rec maxl (a:int) (l:list int) : Tot int (decreases l) =
  match l with | [] -> a | b::t -> maxl (if b > a then b else a) t

(* O1: fixed loop selects the maximum lower bound (invariant sel = a). *)
let rec new_correct (a:int) (l:list int)
  : Lemma (ensures new_scan a a l == maxl a l) (decreases l) =
  match l with | [] -> () | b::t -> new_correct (if b > a then b else a) t

(* O2: result is >= every bound and equals one of them (soundness of dropping others). *)
let rec new_ge (a:int) (l:list int)
  : Lemma (ensures new_scan a a l >= a /\ (forall (b:int). memP b l ==> new_scan a a l >= b))
          (decreases l) =
  match l with | [] -> () | b::t -> new_ge (if b > a then b else a) t

(* O3: refutation of the pre-PR code: concrete reachable witness
   (1<=x) /\ (3<=x) /\ (2<=x): old selects 2, which is weaker than 3. *)
let old_witness () : Lemma (old_scan 1 1 [3;2] == 2 /\ maxl 1 [3;2] == 3 /\ new_scan 1 1 [3;2] == 3) =
  assert_norm (old_scan 1 1 [3;2] == 2);
  assert_norm (maxl 1 [3;2] == 3);
  assert_norm (new_scan 1 1 [3;2] == 3)
