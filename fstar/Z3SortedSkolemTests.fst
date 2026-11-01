module Z3SortedSkolemTests

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module E = Z3SortedSkolem

let primitive (_:sort) : Type0 = bool

let schema : S.checked_schema =
  let s = { S.sorts = []; cases = [] } in
  assert_norm (S.valid s);
  s

unfold let sorts = [bool_sort; bool_sort]

let distinct (vs:V.arguments primitive (S.signature schema) sorts) : prop =
  ~(E.tuple_at (S.signature schema) sorts vs 0 ==
    E.tuple_at (S.signature schema) sorts vs 1)

let joint_choice_has_compatible_coordinates (choice:E.hilbert_choice primitive schema)
  : Lemma (ensures distinct (choice.epsilon sorts distinct)) =
  let witness : V.arguments primitive (S.signature schema) sorts =
    [V.Scalar bool_sort false; V.Scalar bool_sort true] in
  assert_norm (distinct [V.Scalar bool_sort false; V.Scalar bool_sort true]);
  FStar.Classical.exists_intro distinct witness

(* The production ghost choice (FStar.IndefiniteDescription only) is a
   hilbert_choice, so the joint property holds for an actual, constructed
   choice, not only for a hypothetical one: its one chosen tuple has two
   different coordinates, which independent per-coordinate choices could
   not guarantee. *)
let ghost_choice_has_compatible_coordinates ()
  : Lemma (ensures distinct ((E.ghost_choice schema (fun (_:sort) -> false)).E.epsilon sorts distinct)) =
  joint_choice_has_compatible_coordinates (E.ghost_choice schema (fun (_:sort) -> false))
