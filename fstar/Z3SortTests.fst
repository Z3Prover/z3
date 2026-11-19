module Z3SortTests

open Z3AstTheory
module U = Z3UnifiedProof
module A = Z3ArrayTheory
module S = Z3SeqTheory

let integer = SortApp IntSymbol []
let character = SortApp CharSymbol []

let structural_identity ()
  : Lemma (
    integer <> BaseSort "Int" /\
    SortApp (BvSymbol 8) [] <> BaseSort "BV8" /\
    SortApp (BvSymbol 8) [] <> SortApp (BvSymbol 32) [] /\
    SortApp (FiniteFieldSymbol 5) [] <> SortApp (FiniteFieldSymbol 7) [] /\
    SortApp SeqSymbol [integer] <> SortApp SeqSymbol [character] /\
    SortApp (DatatypeSymbol 1) [integer] <> SortApp (DatatypeSymbol 1) [character] /\
    SortApp (ExtensionSymbol 1 2) [integer] <> SortApp (ExtensionSymbol 2 2) [integer] /\
    ArraySort [integer; character] integer <> ArraySort [integer] (ArraySort [character] integer))
  = ()

let malformed_shapes ()
  : Lemma (
    not (valid_sort (SortApp (BvSymbol 0) [])) /\
    not (valid_sort (SortApp (FiniteFieldSymbol 1) [])) /\
    not (valid_sort (SortApp IntSymbol [integer])) /\
    not (valid_sort (SortApp SeqSymbol [])) /\
    not (valid_sort (SortApp ReSymbol [integer])) /\
    not (valid_sort (ArraySort [] integer)) /\
    valid_sort (ArraySort [integer] (SortApp SeqSymbol [ArraySort [character] integer])))
  = ()

let bounded_structural_comparison ()
  : Lemma (
    U.sort_eq_within 1 (SortApp SeqSymbol [integer]) (SortApp SeqSymbol [integer]) == None /\
    U.sort_eq_within 8 (SortApp SeqSymbol [integer]) (SortApp SeqSymbol [integer]) == Some (true, 3) /\
    U.sort_eq_within 8 (SortApp SeqSymbol [integer]) (SortApp SeqSymbol [character]) == Some (false, 5))
  = assert_norm (
    U.sort_eq_within 1 (SortApp SeqSymbol [integer]) (SortApp SeqSymbol [integer]) == None /\
    U.sort_eq_within 8 (SortApp SeqSymbol [integer]) (SortApp SeqSymbol [integer]) == Some (true, 3) /\
    U.sort_eq_within 8 (SortApp SeqSymbol [integer]) (SortApp SeqSymbol [character]) == Some (false, 5))

let nested_array_values (outer:A.arr int (A.arr int int)) (inner:A.arr int int) (i j x:int)
  : Lemma (A.select (A.select (A.store outer i (A.store inner j x)) i) j == x) =
  A.lemma_select_store_same outer i (A.store inner j x);
  A.lemma_select_store_same inner j x

let sequences_of_arrays (a b:A.arr int int)
  : Lemma (
    S.len (S.concat (S.unit a) (S.unit b)) == 2 /\
    S.nth (S.concat (S.unit a) (S.unit b)) 0 == a /\
    S.nth (S.concat (S.unit a) (S.unit b)) 1 == b /\
    S.semantic_prefix [a] [a; b] /\
    S.semantic_contains [a; b] [a] /\
    S.semantic_replace [a; b] [a] [b] == [b; b])
  = ()

let arrays_as_indices (a:A.semantic_arr int int)
                      (outer:A.semantic_arr (A.semantic_arr int int) int) (x:int)
  : Lemma (A.semantic_select (A.semantic_store outer a x) a == x) =
  A.lemma_semantic_store_same outer a x

let permuting_array_values (outer:A.arr int (A.arr int int))
                           (a b:A.arr int int) (i j:int{i <> j})
  : Lemma (
    A.apply_updates outer [(i, a); (j, b)] ==
    A.apply_updates outer [(j, b); (i, a)]) =
  A.lemma_apply_updates_set_eq outer [(i, a); (j, b)] [(j, b); (i, a)]
    (fun _ -> ()) (fun _ _ _ -> ()) (fun _ _ _ -> ())
