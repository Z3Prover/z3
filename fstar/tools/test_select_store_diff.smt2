; select_store_diff -- the array rewrite that `select(store(a,i,x),j) =
; select(a,j)` requires `i <> j`, and is documented (but deliberately
; NOT implemented) in Z3PatternMatchedProofChecker.fst section 4a as a
; known limitation: `the_interpretation` maps all same-sort named
; constants to the same semantic value, so a generic "i <> j" side
; condition can't be discharged by the model this checker uses. There
; is no `match_select_store_diff`/`select_store_diff_leaf_ok` in
; Z3PatternMatchedProofChecker.fst, so any `Rewrite` leaf shaped like
; this will always be logged as unmatched, regardless of what Z3
; actually proves it with.
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const x Int)
(assert (not (= i j)))
(assert (not (= (select (store a i x) j) (select a j))))
(check-sat)
