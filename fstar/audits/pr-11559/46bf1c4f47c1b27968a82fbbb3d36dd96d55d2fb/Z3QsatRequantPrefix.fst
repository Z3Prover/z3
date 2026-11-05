module Z3QsatRequantPrefix
(* Mirrors the PR's loop in qsat.cpp (head 46bf1c4f): for i = n-1 downto 1,
   wrap fml with mk_forall if is_exists(i) else mk_exists; then bind free vars with exists.
   Scope: quantifier-prefix shape only (kind and order), not QE semantic soundness. *)
open FStar.List.Tot

type q = | Ex | All
type lvl = nat

let is_exists (l:nat) : bool = (l % 2 = 0)
let dual_of_is_exists (i:nat) : q = if is_exists i then All else Ex

(* specification: blocks 1..i, outermost first (increasing level) with dual kinds *)
let rec spec (i:nat) : Tot (list (nat & q)) (decreases i) =
  if i = 0 then [] else append (spec (i-1)) [(i, dual_of_is_exists i)]

(* C++ loop: wrap levels n-1 .. 1 successively, each new wrapper goes outside *)
let rec wrap (i:nat) (acc:list (nat & q)) : Tot (list (nat & q)) (decreases i) =
  if i = 0 then acc
  else wrap (i-1) ((i, dual_of_is_exists i) :: acc)

(* loop starts at i = n-1 with acc = [], ends before i = 0 *)
let cpp_prefix (n:nat{n >= 1}) : list (nat & q) = wrap (n-1) []

(* O1: the loop's result is exactly the in-order prefix for levels 1..n-1 *)
let rec wrap_eq (i:nat) (acc:list (nat & q)) : Lemma (ensures wrap i acc == append (spec i) acc) (decreases i) =
  if i = 0 then () else begin
    wrap_eq (i-1) ((i, dual_of_is_exists i) :: acc);
    append_assoc (spec (i-1)) [(i, dual_of_is_exists i)] acc
  end

(* O2: level 1 (first hoisted block) is bound with Ex, same as m_free_vars *)
let o2 () : Lemma (dual_of_is_exists 1 == Ex) = ()

(* O3: adjacent levels get opposite quantifiers (alternation preserved) *)
let o3 (i:nat) : Lemma (dual_of_is_exists i <> dual_of_is_exists (i+1)) = ()

(* O4: concrete 4-level instance: prefix E L1 A L2 E L3 *)
let o4 () : Lemma (cpp_prefix 4 == [(1,Ex);(2,All);(3,Ex)]) =
  assert_norm (cpp_prefix 4 == [(1,Ex);(2,All);(3,Ex)])
