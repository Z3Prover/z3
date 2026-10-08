(*
   Z3SeqTheory.fst

   A self-contained axiomatization, in F*, of the core operations of Z3's
   theory of sequences as implemented by the rewrite rules in
   src/ast/rewriter/seq_rewriter.cpp.

   A sequence is modeled as a finite list over an arbitrary element type
   with decidable equality (`eqtype`); in Z3 the element type is the
   8-bit bit-vector sort used for characters (for str.* symbols) or an
   arbitrary sort (for general seq.* symbols). Using lists gives us
   induction and pattern matching for free while remaining fully
   self-contained (no dependency on FStar.Seq).

   Each operation below corresponds to one Z3 sequence symbol:

     empty     ~  (as seq.empty _)
     unit      ~  (seq.unit x)
     concat    ~  (seq.++ s t) / (str.++ s t)
     len       ~  (seq.len s)  / (str.len s)
     nth       ~  (seq.nth_i s i), the *defined* core accessor,
                  0 <= i < len s (corresponds to seq.nth_i / seq.nth_u
                  restricted to the in-range case)
     at        ~  (seq.at s i)  / (str.at s i)
     extract   ~  (seq.extract s pos len) / (str.substr s pos len)
     reverse   ~  internal `seq_rewriter::mk_seq_reverse` helper
     power     ~  (seq.^ s n) / (str.^ s n)
     is_prefix ~  (seq.prefixof p s) / (str.prefixof p s)
     is_suffix ~  (seq.suffixof p s) / (str.suffixof p s)
     contains  ~  (seq.contains s t) / (str.contains s t)
     replace   ~  (seq.replace s pat rep) / (str.replace s pat rep)
     map       ~  (seq.map f s)
     mapi      ~  (seq.mapi f i s)
     fold_left ~  (seq.foldl f b s)
     fold_lefti ~ (seq.foldli f i b s)
*)
module Z3SeqTheory

(* ----------------------------------------------------------------- *)
(* Sequences                                                          *)
(* ----------------------------------------------------------------- *)

type seq (a:eqtype) = list a

let empty (#a:eqtype) : seq a = []

let unit (#a:eqtype) (x:a) : seq a = [x]

let rec concat (#a:eqtype) (s t:seq a) : seq a =
  match s with
  | [] -> t
  | x :: s' -> x :: concat s' t

(* ----------------------------------------------------------------- *)
(* Length                                                              *)
(* ----------------------------------------------------------------- *)

let rec len (#a:eqtype) (s:seq a) : nat =
  match s with
  | [] -> 0
  | _ :: s' -> 1 + len s'

(* ----------------------------------------------------------------- *)
(* nth / at                                                            *)
(* ----------------------------------------------------------------- *)

(* The defined, in-range element accessor (Z3's seq.nth_i). *)
let rec nth (#a:eqtype) (s:seq a) (i:nat{i < len s}) : a =
  match s with
  | x :: s' -> if i = 0 then x else nth s' (i - 1)

(* Total accessor: empty outside of range, otherwise a singleton. *)
let at (#a:eqtype) (s:seq a) (i:int) : seq a =
  if i < 0 || i >= len s then empty
  else unit (nth s i)

(* ----------------------------------------------------------------- *)
(* drop / take -- helpers used to specify `extract`                   *)
(* ----------------------------------------------------------------- *)

let rec drop (#a:eqtype) (s:seq a) (n:nat) : seq a =
  match s with
  | [] -> []
  | x :: s' -> if n = 0 then s else drop s' (n - 1)

let rec take (#a:eqtype) (s:seq a) (n:nat) : seq a =
  match s with
  | [] -> []
  | x :: s' -> if n = 0 then [] else x :: take s' (n - 1)

(* ----------------------------------------------------------------- *)
(* extract / substr                                                   *)
(* ----------------------------------------------------------------- *)

(* extract s pos ln : the maximal prefix of length min(ln, len s - pos)
   of the suffix of s that starts at position pos; empty when
   pos < 0, ln <= 0, or pos >= len s. *)
let rec extract_nat (#a:eqtype) (s:seq a) (pos:nat) (ln:nat) : seq a =
  match s with
  | [] -> []
  | x :: s' ->
    if pos > 0 then extract_nat s' (pos - 1) ln
    else if ln = 0 then []
    else x :: extract_nat s' 0 (ln - 1)

let extract (#a:eqtype) (s:seq a) (pos:int) (ln:int) : seq a =
  if pos < 0 || ln <= 0 then empty
  else extract_nat s pos ln

(* ----------------------------------------------------------------- *)
(* reverse                                                             *)
(* ----------------------------------------------------------------- *)

let rec reverse (#a:eqtype) (s:seq a) : seq a =
  match s with
  | [] -> []
  | x :: s' -> concat (reverse s') (unit x)

(* ----------------------------------------------------------------- *)
(* power (seq.^ / str.^)                                               *)
(* ----------------------------------------------------------------- *)

let rec power_nat (#a:eqtype) (s:seq a) (n:nat) : seq a =
  if n = 0 then empty else concat s (power_nat s (n - 1))

let power (#a:eqtype) (s:seq a) (n:int) : seq a =
  if n <= 0 then empty else power_nat s n

(* ----------------------------------------------------------------- *)
(* prefix / suffix / contains                                          *)
(* ----------------------------------------------------------------- *)

let rec is_prefix (#a:eqtype) (p s:seq a) : bool =
  match p with
  | [] -> true
  | x :: p' ->
    (match s with
     | [] -> false
     | y :: s' -> x = y && is_prefix p' s')

let is_suffix (#a:eqtype) (p s:seq a) : bool =
  is_prefix (reverse p) (reverse s)

let rec contains (#a:eqtype) (s t:seq a) : bool =
  is_prefix t s ||
  (match s with
   | [] -> false
   | _ :: s' -> contains s' t)

(* ----------------------------------------------------------------- *)
(* replace (first occurrence)                                         *)
(* ----------------------------------------------------------------- *)

(* Z3 convention (see mk_seq_replace): replacing the empty pattern
   prepends the replacement: replace s [] rep = concat rep s. This
   falls out of the definition below since `is_prefix [] s` is always
   true. *)
let rec replace (#a:eqtype) (s pat rep:seq a) : seq a =
  if is_prefix pat s then concat rep (drop s (len pat))
  else
    match s with
    | [] -> []
    | x :: s' -> x :: replace s' pat rep

(* ----------------------------------------------------------------- *)
(* map / mapi / fold_left / fold_lefti                                 *)
(*                                                                      *)
(* These model (seq.map f s), (seq.mapi f i s), (seq.foldl f b s),      *)
(* (seq.foldli f i b s) (OP_SEQ_MAP/MAPI/FOLDL/FOLDLI,                  *)
(* seq_decl_plugin.h:60-63). In Z3 `f` (and `f` applied to a running    *)
(* index, for the `i`-suffixed variants) is an uninterpreted Z3 Array   *)
(* sort value selected via `array.mk_select`; here it is simply an      *)
(* arbitrary F* function, which is a sound abstraction of "any          *)
(* function value" since the rewrite rules below never inspect `f`'s   *)
(* internals -- they only ever apply it (via `select`) to concrete      *)
(* element/index arguments, exactly as modeled by ordinary function     *)
(* application below.                                                   *)
(* ----------------------------------------------------------------- *)

(* map f s : apply f to every element of s, left to right. *)
let rec map (#a #b:eqtype) (f:a -> b) (s:seq a) : seq b =
  match s with
  | [] -> []
  | x :: s' -> f x :: map f s'

(* mapi f i s : apply f to every element of s together with its        *)
(* position, counting up from the starting index i. *)
let rec mapi (#a #b:eqtype) (f:int -> a -> b) (i:int) (s:seq a) : Tot (seq b) (decreases s) =
  match s with
  | [] -> []
  | x :: s' -> f i x :: mapi f (i + 1) s'

(* fold_left f b0 s : left fold of f over s starting from accumulator  *)
(* b0, i.e. f(...f(f(b0,s_0),s_1)...,s_{n-1}). *)
let rec fold_left (#a #b:eqtype) (f:b -> a -> b) (b0:b) (s:seq a) : Tot b (decreases s) =
  match s with
  | [] -> b0
  | x :: s' -> fold_left f (f b0 x) s'

(* fold_lefti f i b0 s : indexed left fold, counting the running index *)
(* up from i as fold_left does with the accumulator. *)
let rec fold_lefti (#a #b:eqtype) (f:int -> b -> a -> b) (i:int) (b0:b) (s:seq a) : Tot b (decreases s) =
  match s with
  | [] -> b0
  | x :: s' -> fold_lefti f (i + 1) (f i b0 x) s'
