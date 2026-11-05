module Pr11551Audit

(* Obligation A (ast_smt2_pp.cpp, concat branch): left-nested binary printing
   of an n-ary concat (n>2) denotes the same bit-vector value as the n-ary
   concat. Values are natural numbers, widths are positive. *)
let cat (a:nat) (b:nat) (wb:nat) : nat = a * pow2 wb + b

(* n=3: the printed form (concat (concat x y) z) vs right-nested semantic *)
let concat3_left_eq_right (x y z:nat) (wy wz:nat)
  : Lemma (cat (cat x y wy) z wz == cat x (cat y z wz) (wy + wz))
  = Math.Lemmas.pow2_plus wy wz;
    assert (cat (cat x y wy) z wz == (x * pow2 wy + y) * pow2 wz + z);
    assert (cat x (cat y z wz) (wy+wz) == x * (pow2 wy * pow2 wz) + (y * pow2 wz + z))

(* n-ary: fold-left over the argument list, tracking running value;
   widths list gives width of each later argument. *)
let rec foldl_cat (acc:nat) (xs: list (nat & nat)) : Tot nat (decreases xs) =
  match xs with
  | [] -> acc
  | (v,w)::t -> foldl_cat (cat acc v w) t   (* (concat acc next) *)

let rec total_w (xs: list (nat & nat)) : nat =
  match xs with [] -> 0 | (_,w)::t -> w + total_w t

let rec sem (acc:nat) (xs: list (nat & nat)) : Tot nat (decreases xs) =
  match xs with
  | [] -> acc
  | (v,w)::t -> sem (acc * pow2 w + v) t

(* A left fold of binary concat equals the positional n-ary semantics
   (the printer's first two args are folded, then each remaining arg). *)
let rec foldl_is_sem (acc:nat) (xs: list (nat & nat))
  : Lemma (ensures foldl_cat acc xs == sem acc xs) (decreases xs)
  = match xs with
    | [] -> ()
    | (v,w)::t -> foldl_is_sem (cat acc v w) t

(* Obligation B (qsat.cpp, qsat_qe answer re-quantification): level parity.
   In qsat_qe mode level 0 holds free vars, level 1 is the first hoisted
   block; is_exists i = (i % 2 = 0). The patch wraps level i with forall when
   is_exists i, else exists. Since the hoisted formula is the negation of the
   input, the input-side quantifier is the dual. *)
let is_exists (i:nat) : bool = i % 2 = 0
type q = | QForall | QExists
let wrap_q (i:nat) : q = if is_exists i then QForall else QExists

(* Level 1 (outermost hoisted block, a forall of the negated matrix) becomes
   exists of the input; levels strictly alternate. *)
let level1_exists () : Lemma (wrap_q 1 == QExists) = ()
let alternates (i:nat) : Lemma (wrap_q i <> wrap_q (i+1)) = ()

(* Obligation C: loop order. The patch iterates i = n-1 down to 1 wrapping the
   current formula, so the final prefix lists levels 1..n-1 outermost-first. *)
let rec wrap_down (i:nat) (acc: list nat) : Tot (list nat) (decreases i) =
  if i = 0 then acc else wrap_down (i-1) (i :: acc)
  (* wrapping level i outside the current formula prepends it to the prefix *)

let rec app (a b: list nat) : list nat = match a with [] -> b | h::t -> h :: app t b
let rec app_assoc (a b c: list nat) : Lemma (app (app a b) c == app a (app b c)) = match a with [] -> () | _::t -> app_assoc t b c

let rec init_range (n:nat) : Tot (list nat) (decreases n) =
  if n = 0 then [] else app (init_range (n-1)) [n]

let rec wrap_down_sorted (i:nat) (acc: list nat)
  : Lemma (ensures wrap_down i acc == app (init_range i) acc) (decreases i)
  = if i = 0 then () else begin
      wrap_down_sorted (i-1) (i::acc);
      app_assoc (init_range (i-1)) [i] acc
    end
