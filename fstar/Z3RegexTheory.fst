(*
   Z3RegexTheory.fst

   A self-contained axiomatization, in F*, of Z3's theory of regular
   expressions over sequences, built on top of Z3SeqTheory.fst. A
   regular language is modeled directly by its semantics: a predicate
   on finite sequences (`lang a = seq a -> Type0`), i.e. the set of
   words it accepts. This gives every combinator below a denotational
   meaning for free and lets closure/identity lemmas be proved by
   simple (in)equivalence-of-predicates reasoning, without committing
   to any particular automaton or term representation.

   Each combinator corresponds to one Z3 regex symbol from
   src/ast/seq_decl_plugin.h's `seq_op_kind` (the `OP_RE_*` and the
   regex-relevant `OP_SEQ_*` constants):

     re_empty    ~  (re.empty re)              [OP_RE_EMPTY_SET]
     re_full     ~  (re.all re) / (re.allchar)* [OP_RE_FULL_SEQ_SET]
     re_allchar  ~  (re.allchar re)             [OP_RE_FULL_CHAR_SET]
     re_of_pred  ~  internal: a character class guarded by a predicate
                    [OP_RE_OF_PRED], used also to model OP_RE_RANGE
     re_to_re    ~  (seq.to_re s)               [OP_SEQ_TO_RE]
     re_unit     ~  (seq.to_re (seq.unit x)), the single-symbol regex
                    ("unit") that every character/range literal bottoms
                    out at
     re_concat   ~  (re.++ r1 r2)               [OP_RE_CONCAT]
     re_union    ~  (re.union r1 r2)            [OP_RE_UNION]
     re_inter    ~  (re.inter r1 r2)       (a.k.a. intersect)
                                                 [OP_RE_INTERSECT]
     re_compl    ~  (re.complement r)           [OP_RE_COMPLEMENT]
     re_diff     ~  (re.diff r1 r2)             [OP_RE_DIFF]
     re_xor      ~  (xor r1 r2) on regular sets [OP_RE_XOR]
     re_star     ~  (re.* r)                    [OP_RE_STAR]
     re_plus     ~  (re.+ r)                    [OP_RE_PLUS]
     re_opt      ~  (re.opt r)                  [OP_RE_OPTION]
     re_loop     ~  (re.loop r lo hi), bounded   [OP_RE_LOOP, 2 args]
     re_loop_lo  ~  (re.loop r lo), unbounded    [OP_RE_LOOP, 1 arg]
     re_reverse  ~  internal reverse-of-language helper
                                                 [OP_RE_REVERSE]

   The element type `a` is the same arbitrary `eqtype` used throughout
   Z3SeqTheory (characters for str.*/re.*, or a general element sort
   for seq.*/re.* over non-string sequences).

   Existentials of arity >= 2 (as needed by re_concat) are modeled, per
   FStar.Classical's own recommendation, by tupling the witnesses and
   letting a pair-typed existential stand for the two-variable one;
   `intro_concat`/`elim_concat` package this up once and for all below.
*)
module Z3RegexTheory

open Z3SeqTheory
module Classical = FStar.Classical

(* ----------------------------------------------------------------- *)
(* Languages: a regular language is its set of accepted words         *)
(* ----------------------------------------------------------------- *)

type lang (a:eqtype) = seq a -> prop

(* Word membership, spelled out for readability in statements below. *)
let mem (#a:eqtype) (w:seq a) (l:lang a) : prop = l w

(* Language equivalence: same accepted words. *)
let equiv (#a:eqtype) (l1 l2:lang a) : prop =
  forall (w:seq a). mem w l1 <==> mem w l2

(* ----------------------------------------------------------------- *)
(* Base languages                                                      *)
(* ----------------------------------------------------------------- *)

(* re.empty: accepts nothing. *)
let re_empty (#a:eqtype) : lang a = fun _ -> False

(* re.all: accepts every word. *)
let re_full (#a:eqtype) : lang a = fun _ -> True

(* (seq.to_re s): the singleton language containing exactly s. *)
let re_to_re (#a:eqtype) (s:seq a) : lang a = fun w -> w == s

(* A single symbol constrained by a predicate p -- the general shape
   of a character class / range literal (re.range, re.of_pred). *)
let re_of_pred (#a:eqtype) (p:a -> bool) : lang a =
  fun w -> (match w with | [x] -> p x == true | _ -> False)

(* re.allchar: any single symbol. *)
let re_allchar (#a:eqtype) : lang a = re_of_pred (fun _ -> true)

(* re.range lo hi, parameterized by an explicit "in range" test since
   `a` carries no built-in order; this is exactly how Z3 treats a
   range literal once its two endpoints have been resolved into a
   membership predicate. *)
let re_range (#a:eqtype) (in_range:a -> bool) : lang a = re_of_pred in_range

(* (seq.to_re (seq.unit x)): the "unit" regex -- the single-symbol
   literal language used to build up every character/range regex. *)
let re_unit (#a:eqtype) (x:a) : lang a = re_to_re (unit x)

(* ----------------------------------------------------------------- *)
(* Concatenation                                                      *)
(* ----------------------------------------------------------------- *)

let re_concat (#a:eqtype) (l1 l2:lang a) : lang a =
  fun w -> exists (p:(seq a & seq a)). w == concat (fst p) (snd p) /\ mem (fst p) l1 /\ mem (snd p) l2

(* ----------------------------------------------------------------- *)
(* Boolean combinators                                                 *)
(* ----------------------------------------------------------------- *)

let re_union (#a:eqtype) (l1 l2:lang a) : lang a = fun w -> mem w l1 \/ mem w l2

let re_inter (#a:eqtype) (l1 l2:lang a) : lang a = fun w -> mem w l1 /\ mem w l2

let re_compl (#a:eqtype) (l:lang a) : lang a = fun w -> ~(mem w l)

(* r \ s = r & not(s). Z3: OP_RE_DIFF, see seq_decl_plugin.cpp's
   `rex::info::diff` comment "Lambda(r \ s) is contained in Lambda(r)". *)
let re_diff (#a:eqtype) (l1 l2:lang a) : lang a = re_inter l1 (re_compl l2)

(* symmetric difference. *)
let re_xor (#a:eqtype) (l1 l2:lang a) : lang a =
  fun w -> (mem w l1 /\ ~(mem w l2)) \/ (~(mem w l1) /\ mem w l2)

(* ----------------------------------------------------------------- *)
(* Iteration: power, star, plus, opt, loop                             *)
(* ----------------------------------------------------------------- *)

(* L^n : words formed by concatenating exactly n words of L. *)
let rec re_pow (#a:eqtype) (l:lang a) (n:nat) : lang a =
  if n = 0 then re_to_re empty
  else re_concat l (re_pow l (n - 1))

(* re.* : zero or more repetitions. *)
let re_star (#a:eqtype) (l:lang a) : lang a =
  fun w -> exists (n:nat). mem w (re_pow l n)

(* re.+ : one or more repetitions. *)
let re_plus (#a:eqtype) (l:lang a) : lang a =
  fun w -> exists (n:nat{n >= 1}). mem w (re_pow l n)

(* re.opt : zero or one occurrence. *)
let re_opt (#a:eqtype) (l:lang a) : lang a = re_union (re_to_re empty) l

(* re.loop r lo hi (bounded): between lo and hi repetitions, inclusive. *)
let re_loop (#a:eqtype) (l:lang a) (lo hi:nat) : lang a =
  fun w -> exists (n:nat{lo <= n /\ n <= hi}). mem w (re_pow l n)

(* re.loop r lo (unbounded): at least lo repetitions.
   Matches Z3's single-argument re.loop, i.e. `i1.loop(lower_bound, UINT_MAX)`
   with the upper bound left unconstrained. *)
let re_loop_lo (#a:eqtype) (l:lang a) (lo:nat) : lang a =
  re_concat (re_pow l lo) (re_star l)

(* ----------------------------------------------------------------- *)
(* Reverse                                                             *)
(* ----------------------------------------------------------------- *)

(* re.reverse: a word is in reverse(L) iff its reversal is in L. *)
let re_reverse (#a:eqtype) (l:lang a) : lang a = fun w -> mem (reverse w) l

(* ================================================================= *)
(* Helper facts about concat/reverse reused throughout                *)
(* ================================================================= *)

let rec lemma_concat_empty_r (#a:eqtype) (s:seq a)
  : Lemma (concat s empty == s)
  = match s with
    | [] -> ()
    | _ :: s' -> lemma_concat_empty_r s'

let lemma_concat_empty_l (#a:eqtype) (s:seq a)
  : Lemma (concat empty s == s)
  = ()

let rec lemma_concat_assoc (#a:eqtype) (s t u:seq a)
  : Lemma (concat (concat s t) u == concat s (concat t u))
  = match s with
    | [] -> ()
    | _ :: s' -> lemma_concat_assoc s' t u

let rec lemma_reverse_concat (#a:eqtype) (s t:seq a)
  : Lemma (reverse (concat s t) == concat (reverse t) (reverse s))
  = match s with
    | [] -> lemma_concat_empty_r (reverse t)
    | x :: s' -> lemma_reverse_concat s' t; lemma_concat_assoc (reverse t) (reverse s') (unit x)

let rec lemma_reverse_reverse (#a:eqtype) (s:seq a)
  : Lemma (reverse (reverse s) == s)
  = match s with
    | [] -> ()
    | x :: s' -> lemma_reverse_reverse s'; lemma_reverse_concat (reverse s') (unit x)

(* ----------------------------------------------------------------- *)
(* Generic packaging of a 2-witness existential (used by re_concat)   *)
(* ----------------------------------------------------------------- *)

let intro2 (#a:eqtype) (q:((seq a & seq a) -> prop)) (w1 w2:seq a)
  : Lemma (requires q (w1, w2)) (ensures exists (p:(seq a & seq a)). q p)
  = Classical.exists_intro q (w1, w2)

(* Membership in a concatenation, built from explicit witnesses. *)
let intro_concat (#a:eqtype) (l1 l2:lang a) (w w1 w2:seq a)
  : Lemma (requires w == concat w1 w2 /\ mem w1 l1 /\ mem w2 l2)
          (ensures mem w (re_concat l1 l2))
  = intro2 (fun p -> w == concat (fst p) (snd p) /\ mem (fst p) l1 /\ mem (snd p) l2) w1 w2

(* Eliminating membership in a concatenation: [f] receives the two
   witnesses as ordinary program variables. *)
let elim_concat (#a:eqtype) (l1 l2:lang a) (w:seq a) (goal:prop)
          (f: (w1:seq a -> w2:seq a -> Lemma (requires w == concat w1 w2 /\ mem w1 l1 /\ mem w2 l2) (ensures goal)))
  : Lemma (requires mem w (re_concat l1 l2)) (ensures goal)
  = Classical.exists_elim goal
      #(seq a & seq a)
      #(fun p -> w == concat (fst p) (snd p) /\ mem (fst p) l1 /\ mem (snd p) l2)
      ()
      (fun p -> f (fst p) (snd p))

(* ================================================================= *)
(* Concatenation: associativity, empty word unit                      *)
(* ================================================================= *)

let lemma_concat_assoc_lang_fwd (#a:eqtype) (l1 l2 l3:lang a) (w:seq a)
  : Lemma (requires mem w (re_concat (re_concat l1 l2) l3))
          (ensures mem w (re_concat l1 (re_concat l2 l3)))
  = elim_concat (re_concat l1 l2) l3 w (mem w (re_concat l1 (re_concat l2 l3))) (fun w12 w3 ->
      elim_concat l1 l2 w12 (mem w (re_concat l1 (re_concat l2 l3))) (fun w1 w2 ->
        lemma_concat_assoc w1 w2 w3;
        intro_concat l2 l3 (concat w2 w3) w2 w3;
        intro_concat l1 (re_concat l2 l3) w w1 (concat w2 w3)))

let lemma_concat_assoc_lang_bwd (#a:eqtype) (l1 l2 l3:lang a) (w:seq a)
  : Lemma (requires mem w (re_concat l1 (re_concat l2 l3)))
          (ensures mem w (re_concat (re_concat l1 l2) l3))
  = elim_concat l1 (re_concat l2 l3) w (mem w (re_concat (re_concat l1 l2) l3)) (fun w1 w23 ->
      elim_concat l2 l3 w23 (mem w (re_concat (re_concat l1 l2) l3)) (fun w2 w3 ->
        lemma_concat_assoc w1 w2 w3;
        intro_concat l1 l2 (concat w1 w2) w1 w2;
        intro_concat (re_concat l1 l2) l3 w (concat w1 w2) w3))

(* (r1 . r2) . r3  ==  r1 . (r2 . r3), as languages. *)
let lemma_concat_assoc_lang (#a:eqtype) (l1 l2 l3:lang a)
  : Lemma (equiv (re_concat (re_concat l1 l2) l3) (re_concat l1 (re_concat l2 l3)))
  = let proof (w:seq a)
      : Lemma (mem w (re_concat (re_concat l1 l2) l3) <==> mem w (re_concat l1 (re_concat l2 l3))) =
      Classical.move_requires (lemma_concat_assoc_lang_fwd l1 l2 l3) w;
      Classical.move_requires (lemma_concat_assoc_lang_bwd l1 l2 l3) w
    in
    Classical.forall_intro proof

(* The empty word is a left/right unit for concatenation at the
   language level: {""} . r == r == r . {""}. *)
let lemma_concat_unit_r (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_concat l (re_to_re empty)) l)
  = let fwd (w:seq a) : Lemma (requires mem w (re_concat l (re_to_re empty))) (ensures mem w l) =
      elim_concat l (re_to_re empty) w (mem w l) (fun w1 w2 -> lemma_concat_empty_r w1)
    in
    let bwd (w:seq a) : Lemma (requires mem w l) (ensures mem w (re_concat l (re_to_re empty))) =
      lemma_concat_empty_r w;
      intro_concat l (re_to_re empty) w w empty
    in
    let proof (w:seq a) : Lemma (mem w (re_concat l (re_to_re empty)) <==> mem w l) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

let lemma_concat_unit_l (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_concat (re_to_re empty) l) l)
  = let fwd (w:seq a) : Lemma (requires mem w (re_concat (re_to_re empty) l)) (ensures mem w l) =
      elim_concat (re_to_re empty) l w (mem w l) (fun w1 w2 -> ())
    in
    let bwd (w:seq a) : Lemma (requires mem w l) (ensures mem w (re_concat (re_to_re empty) l)) =
      intro_concat (re_to_re empty) l w empty w
    in
    let proof (w:seq a) : Lemma (mem w (re_concat (re_to_re empty) l) <==> mem w l) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* ----------------------------------------------------------------- *)
(* Boolean combinators: commutativity, double complement, De Morgan   *)
(* These are pure classical propositional facts about `mem`, with no  *)
(* existentials to eliminate, so Z3 discharges them directly.         *)
(* ----------------------------------------------------------------- *)

let lemma_union_comm (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_union l1 l2) (re_union l2 l1))
  = ()

let lemma_inter_comm (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_inter l1 l2) (re_inter l2 l1))
  = ()

(* Classical fact (decided by the SMT backend): complementing twice
   is the identity. *)
let lemma_compl_compl (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_compl (re_compl l)) l)
  = ()

(* De Morgan, as used to justify modeling diff/xor via union/inter/compl. *)
let lemma_diff_is_inter_compl (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_diff l1 l2) (re_inter l1 (re_compl l2)))
  = ()

let lemma_xor_is_union_diff (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_xor l1 l2) (re_union (re_diff l1 l2) (re_diff l2 l1)))
  = ()

let lemma_union_inter_compl_demorgan (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_compl (re_union l1 l2)) (re_inter (re_compl l1) (re_compl l2)))
  = ()

(* ----------------------------------------------------------------- *)
(* Star / plus / opt / loop identities                                 *)
(* ----------------------------------------------------------------- *)

(* The empty word is always in L*. *)
let lemma_star_nil (#a:eqtype) (l:lang a)
  : Lemma (mem empty (re_star l))
  = Classical.exists_intro (fun (n:nat) -> mem empty (re_pow l n)) 0

(* L is contained in L* (one repetition). *)
let lemma_star_contains_self (#a:eqtype) (l:lang a) (w:seq a)
  : Lemma (requires mem w l) (ensures mem w (re_star l))
  = lemma_concat_empty_r w;
    intro_concat l (re_pow l 0) w w empty;
    Classical.exists_intro (fun (n:nat) -> mem w (re_pow l n)) 1

(* Unfolding equation: L-star equals (the empty word) union (L . L-star). *)
let lemma_star_unfold_fwd (#a:eqtype) (l:lang a) (w:seq a)
  : Lemma (requires mem w (re_star l))
          (ensures mem w (re_union (re_to_re empty) (re_concat l (re_star l))))
  = Classical.exists_elim (mem w (re_union (re_to_re empty) (re_concat l (re_star l))))
      #nat #(fun n -> mem w (re_pow l n)) ()
      (fun n ->
        if n = 0 then ()
        else
          elim_concat l (re_pow l (n - 1)) w
            (mem w (re_union (re_to_re empty) (re_concat l (re_star l)))) (fun w1 w2 ->
              Classical.exists_intro (fun (m:nat) -> mem w2 (re_pow l m)) (n - 1);
              intro_concat l (re_star l) w w1 w2))

let lemma_star_unfold_bwd (#a:eqtype) (l:lang a) (w:seq a)
  : Lemma (requires mem w (re_union (re_to_re empty) (re_concat l (re_star l))))
          (ensures mem w (re_star l))
  = if mem w (re_to_re empty) then Classical.exists_intro (fun (n:nat) -> mem w (re_pow l n)) 0
    else
      elim_concat l (re_star l) w (mem w (re_star l)) (fun w1 w2 ->
        Classical.exists_elim (mem w (re_star l)) #nat #(fun m -> mem w2 (re_pow l m)) ()
          (fun m ->
            intro_concat l (re_pow l m) w w1 w2;
            Classical.exists_intro (fun (n:nat) -> mem w (re_pow l n)) (m + 1)))

let lemma_star_unfold (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_star l) (re_union (re_to_re empty) (re_concat l (re_star l))))
  = let proof (w:seq a)
      : Lemma (mem w (re_star l) <==> mem w (re_union (re_to_re empty) (re_concat l (re_star l)))) =
      Classical.move_requires (lemma_star_unfold_fwd l) w;
      Classical.move_requires (lemma_star_unfold_bwd l) w
    in
    Classical.forall_intro proof

(* L+ == L . L*  (plus is "at least one" repetition). *)
let lemma_plus_is_concat_star_fwd (#a:eqtype) (l:lang a) (w:seq a)
  : Lemma (requires mem w (re_plus l)) (ensures mem w (re_concat l (re_star l)))
  = Classical.exists_elim (mem w (re_concat l (re_star l)))
      #(n:nat{n >= 1}) #(fun n -> mem w (re_pow l n)) ()
      (fun n ->
        elim_concat l (re_pow l (n - 1)) w (mem w (re_concat l (re_star l))) (fun w1 w2 ->
          Classical.exists_intro (fun (m:nat) -> mem w2 (re_pow l m)) (n - 1);
          intro_concat l (re_star l) w w1 w2))

let lemma_plus_is_concat_star_bwd (#a:eqtype) (l:lang a) (w:seq a)
  : Lemma (requires mem w (re_concat l (re_star l))) (ensures mem w (re_plus l))
  = elim_concat l (re_star l) w (mem w (re_plus l)) (fun w1 w2 ->
      Classical.exists_elim (mem w (re_plus l)) #nat #(fun m -> mem w2 (re_pow l m)) ()
        (fun m ->
          intro_concat l (re_pow l m) w w1 w2;
          Classical.exists_intro (fun (n:nat{n >= 1}) -> mem w (re_pow l n)) (m + 1)))

let lemma_plus_is_concat_star (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_plus l) (re_concat l (re_star l)))
  = let proof (w:seq a) : Lemma (mem w (re_plus l) <==> mem w (re_concat l (re_star l))) =
      Classical.move_requires (lemma_plus_is_concat_star_fwd l) w;
      Classical.move_requires (lemma_plus_is_concat_star_bwd l) w
    in
    Classical.forall_intro proof

(* re.loop r lo lo == L^lo, i.e. a degenerate loop is exact repetition. *)
let lemma_loop_exact (#a:eqtype) (l:lang a) (n:nat)
  : Lemma (equiv (re_loop l n n) (re_pow l n))
  = let fwd (w:seq a) : Lemma (requires mem w (re_loop l n n)) (ensures mem w (re_pow l n)) =
      Classical.exists_elim (mem w (re_pow l n)) #(m:nat{n <= m /\ m <= n}) #(fun m -> mem w (re_pow l m)) () (fun m -> ())
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_pow l n)) (ensures mem w (re_loop l n n)) =
      Classical.exists_intro (fun (m:nat{n <= m /\ m <= n}) -> mem w (re_pow l m)) n
    in
    let proof (w:seq a) : Lemma (mem w (re_loop l n n) <==> mem w (re_pow l n)) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* re.opt r == re.loop r 0 1. *)
let lemma_opt_is_loop_0_1 (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_opt l) (re_loop l 0 1))
  = let fwd (w:seq a) : Lemma (requires mem w (re_opt l)) (ensures mem w (re_loop l 0 1)) =
      if mem w (re_to_re empty) then
        Classical.exists_intro (fun (m:nat{0 <= m /\ m <= 1}) -> mem w (re_pow l m)) 0
      else begin
        lemma_concat_empty_r w;
        intro_concat l (re_pow l 0) w w empty;
        Classical.exists_intro (fun (m:nat{0 <= m /\ m <= 1}) -> mem w (re_pow l m)) 1
      end
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_loop l 0 1)) (ensures mem w (re_opt l)) =
      Classical.exists_elim (mem w (re_opt l)) #(m:nat{0 <= m /\ m <= 1}) #(fun m -> mem w (re_pow l m)) ()
        (fun m ->
          if m = 0 then ()
          else elim_concat l (re_pow l 0) w (mem w (re_opt l)) (fun w1 w2 -> lemma_concat_empty_r w1))
    in
    let proof (w:seq a) : Lemma (mem w (re_opt l) <==> mem w (re_loop l 0 1)) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* re.loop r lo (unbounded) == L^lo . L*. This is definitional, stated
   here to make the correspondence with re_loop_lo explicit. *)
let lemma_loop_lo_def (#a:eqtype) (l:lang a) (lo:nat)
  : Lemma (equiv (re_loop_lo l lo) (re_concat (re_pow l lo) (re_star l)))
  = ()

(* ----------------------------------------------------------------- *)
(* Reverse identities                                                  *)
(* ----------------------------------------------------------------- *)

(* reverse is an involution at the language level. *)
let lemma_reverse_reverse_lang (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_reverse (re_reverse l)) l)
  = let proof (w:seq a) : Lemma (mem w (re_reverse (re_reverse l)) <==> mem w l) =
      lemma_reverse_reverse w
    in
    Classical.forall_intro proof

(* reverse distributes over concat by swapping the operands:
   reverse(L1 . L2) == reverse(L2) . reverse(L1). *)
let lemma_reverse_concat_lang_fwd (#a:eqtype) (l1 l2:lang a) (w:seq a)
  : Lemma (requires mem w (re_reverse (re_concat l1 l2)))
          (ensures mem w (re_concat (re_reverse l2) (re_reverse l1)))
  = elim_concat l1 l2 (reverse w) (mem w (re_concat (re_reverse l2) (re_reverse l1))) (fun w1 w2 ->
      lemma_reverse_concat w1 w2;
      lemma_reverse_reverse w;
      lemma_reverse_reverse w1;
      lemma_reverse_reverse w2;
      intro_concat (re_reverse l2) (re_reverse l1) w (reverse w2) (reverse w1))

let lemma_reverse_concat_lang_bwd (#a:eqtype) (l1 l2:lang a) (w:seq a)
  : Lemma (requires mem w (re_concat (re_reverse l2) (re_reverse l1)))
          (ensures mem w (re_reverse (re_concat l1 l2)))
  = elim_concat (re_reverse l2) (re_reverse l1) w (mem w (re_reverse (re_concat l1 l2))) (fun u1 u2 ->
      lemma_reverse_concat u1 u2;
      intro_concat l1 l2 (reverse w) (reverse u2) (reverse u1))

let lemma_reverse_concat_lang (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_reverse (re_concat l1 l2)) (re_concat (re_reverse l2) (re_reverse l1)))
  = let proof (w:seq a)
      : Lemma (mem w (re_reverse (re_concat l1 l2)) <==> mem w (re_concat (re_reverse l2) (re_reverse l1))) =
      Classical.move_requires (lemma_reverse_concat_lang_fwd l1 l2) w;
      Classical.move_requires (lemma_reverse_concat_lang_bwd l1 l2) w
    in
    Classical.forall_intro proof
