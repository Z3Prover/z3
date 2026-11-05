module SwineAudit4
(* Semantic model of delta ced49cb vs 317d28d in PR 11211 (three changed functions). *)

(* O1: algebraic_numbers::to_rational returns true iff rational; r unchanged on false *)
type anum = | Basic : n:int -> d:pos -> anum | Irr : anum
let to_rational (a:anum) (r:(int & int)) : (bool & (int & int)) =
  match a with
  | Basic n d -> (true, (n, d))
  | Irr -> (false, r)

let ob1_irrational (r:(int & int)) : Lemma (to_rational Irr r == (false, r)) = ()
let ob1_basic (n:int) (d:pos) (r:(int & int))
  : Lemma (to_rational (Basic n d) r == (true, (n, d))) = ()

(* O2: solver::init_model sets flag from lp().init_model() result; flag false on failure *)
let init_flag (guard:bool) (lp_ok:bool) : bool = if guard then lp_ok else false
let ob2 (guard lp_ok:bool) : Lemma (init_flag guard lp_ok ==> lp_ok /\ guard) = ()

(* O3: get_power_value. Value domain: rationals n/d; integer iff d = 1 *)
type rat = { n:int; d:pos }
let is_int (q:rat) = q.d = 1
type src =
  | Numeral : rat -> src
  | NraRat : rat -> src
  | NraIrr : src
  | Lp : rat -> src
let get_power_value (s:src) (nra:bool) (initialized:bool) : option rat =
  match s with
  | Numeral q -> Some q
  | _ ->
    if not nra && not initialized then None
    else (match s with
          | NraRat q -> if nra && is_int q then Some q else None
          | NraIrr -> None
          | Lp q -> if not nra && is_int q then Some q else None
          | _ -> None)

(* Environment assumption (SASSERT in C++): Int-sorted numerals are integers *)
let ob3_integer (s:src) (nra init:bool)
  : Lemma (requires (match s with Numeral q -> is_int q | _ -> true))
          (ensures (match get_power_value s nra init with Some q -> is_int q | None -> True)) = ()
let ob3_irrational_rejected (nra init:bool) : Lemma (get_power_value NraIrr nra init == None) = ()
let ob3_lp_needs_init (q:rat) : Lemma (get_power_value (Lp q) false false == None) = ()
let ob3_nra_no_init (q:rat) : Lemma (requires is_int q)
  (ensures get_power_value (NraRat q) true false == Some q) = ()
