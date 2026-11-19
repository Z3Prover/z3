# Batch 2: P1 source applicability follow-up

Status: source-tracing stage complete. Source was read as text only. No C++
was executed, built, imported or modified. This follow-up does not add a new
Dafny verdict or assert a native SAT/UNSAT result. Continue the scheduled audit.

## Identity and conclusion

Audited production head: `71ec455a18702fe695d0c924a535ff9f385bd58d`.
Existing report commit: `69b9548ea0b4fad73762f95d5633b21571706d70`.
`git diff <audited-head> -- src` was empty; captured source files were also
individually matched against immutable Git blobs. Companion
`nfv2-p1-source-inventory.json` contains exact line excerpts and blob/hash IDs.

The original P1 shape is representable by the actual facet entry points;
opaque variables are not normalized into character-sized tokens. The selected
direct sequence-rewriter path does not eliminate this symbolic expression.
The disputed prune precedes the character-length gate. It disables the
original obligation, so later forward substitutions cannot restore that
obligation. These are source-grounded applicability facts, not a demonstration
that a complete native solver returns an incorrect answer.

## Entry, normalization and comparison predicates

1. `src/smt/theory_nseq.cpp:474-523` handles `str.contains`; its false branch
   at 518-520 directly adds a negative obligation using `tokenize` on both
   arguments. The selected expression is `not contains(X ++ "a" ++ Y,
   X ++ "b")`, with distinct opaque String variables X and Y.
2. `src/smt/theory_nseq.cpp:342-345` first uses ambient tokenization, then
   applies already-recorded root substitutions. Therefore any conclusion
   retaining symbolic X/Y requires that no earlier substitution has expanded
   them. `src/ast/seq/seq_eq_facet.cpp:104-150` implements those substitutions.
3. `src/ast/seq/seq_ambient_context.h:161-169` delegates to
   `src/ast/seq_decl_plugin.cpp:1040-1055`: concatenations are flattened,
   literal strings split into units, empty strings omitted, and other terms
   retained unchanged. The resulting vectors can therefore be
   `[X,unit(a),Y]` and `[X,unit(b)]`; no one-character invariant is imposed
   on X or Y. The convenience facet entry also uses this tokenization
   (`src/ast/seq/seq_ncontains_facet.h:110-118`).
4. `src/ast/rewriter/seq_rewriter.cpp:1529-1634` was inspected for the same
   direct expression, with X/Y opaque and no prior substitution. The words
   are not ground or all-unit, have no pointer-identical token window, and
   have no known finite haystack upper bound. Boundary trimming cannot prove
   nonoverlap for the opaque boundary tokens (1490-1526). Neither the singleton
   unit rule nor the single-character-needle rule applies. This selected
   rewriter invocation falls through; this is not coverage of every tactic
   or preprocessing configuration.
5. In `src/ast/seq/seq_ncontains_facet.cpp:128-141`, token position zero skips
   the identical X pointer and sees distinct constant units; position one
   returns unknown immediately for `unit(a)` versus X. The distinctness
   predicate is grounded by `src/ast/ast.cpp:1612-1622`,
   `src/ast/seq_decl_plugin.cpp:782-797` (unit injectivity), and
   `src/ast/char_decl_plugin.cpp:145-149` (distinct character constants).

## Earlier and later processing

Production plugin order is explicit in `src/smt/theory_nseq.cpp:196-206`:
equations, disequalities, arithmetic, powers, membership bounds, word
templates and membership precede negative containment. The search engine
executes plugins in this order and repeats rounds
(`src/util/stx_search_tree.h:972-991`). Earlier plugins can matter; ordering
must not be treated as an assumption that they never run.

An existing equation X = "aa" can invalidate the symbolic-token scenario:
`src/ast/seq/seq_eq_facet.cpp:290-307` broadcasts acyclic variable
definitions, and 373-391 broadcasts substitutions to sibling facets and adds
the corresponding length equality. Thus simply pinning X/Y by native word
equalities is NOT a justified end-to-end reproduction of the published model
witness. With no relevant active equations, arithmetic propagation itself
only iterates the equation queue (`src/smt/seq_solver_facet.cpp:247-264`).

Word-template processing is not an unconditional expansion of every variable:
it first requires a suitable membership candidate, and specifically marks
variables connected through negative containment dirty
(`src/ast/seq/seq_mem_facet.cpp:1160-1258`, especially 1217-1222).
No complete reachability proof through all earlier facets is claimed.

In `src/ast/seq/seq_ncontains_facet.cpp:264-301`, the selected token scan
sets `first_undef_pos=1` and replaces the obligation with the tail
`[unit(a),Y]`, retaining needle `[X,unit(b)]`. Replacement copies the needle
and dependency before appending, and marks the original inactive (43-50).
The scan continues with the appended obligation in the same pass.

The exact valuation X="aa", Y="b", a='a', b='b' gives original "aaab" and
needle "aab", but the tail is "ab". Occurrence at character offset one is
lost. The published Dafny evidence establishes this valuation-level
inequivalence; this stage does not repeat those verifier checks.

Literal-needle lowering follows pruning (304-340), and the all-unit branch
also follows it (345-373); neither makes the original symbolic needle
concrete retroactively. The character-length gate is later still (392-423).
If the arithmetic facet implies the SHORTENED haystack is shorter than the
needle, it discharges only the replacement. For the witness, the shortened
lengths would be 2 and 3. This is a conditional source continuation, not a
claim about an actual arithmetic model or native run.

Substitution visits active obligations only (52-67). Consequently it updates
the replacement, not the disabled original; qhead rewind does not reconstruct
the removed prefix. Ordinary trail backtracking may restore the earlier
state, so this is not a claim that the original can never reappear on another
branch. Model completion can later substitute concrete candidate values
(`src/ast/seq/seq_eq_facet.cpp:1411-1465,1673-1718`), but that alone does not
repair the transformation within an already-shortened branch.

Satisfaction is the conjunction of installed facets; the search engine clones
a satisfied snapshot (`src/util/stx_search_tree.h:1072-1118`). SAT reconciliation
with the ambient SMT context is additional work
(`src/smt/theory_nseq.cpp:1068-1251`). These gates and the actual resulting
model are NOT established by this source trace.

## Crash-oriented observations and coverage handoff

The user explicitly clarified scope as logical correctness AND possible
user-space crashes. Continue with bounds, nullability, lifetimes/reallocation,
overflow and undo invariants as appropriate; this is not an exploit audit.

For this specific loop, the empty-needle conflict precedes arithmetic on
windows (232-236). When a window exists and the needle is nonempty,
`max_pos=h_size-n_size <= UINT_MAX-1`, so `max_pos+1` is nonzero and the
later finite-unit expansion denominator cannot wrap to zero. Valid window
indices also keep `pos+k < h_size`. These are local arithmetic observations,
not machine-checked C++ safety guarantees.

`replace_with_tail` copies the needle and dependency before vector append;
its caller immediately increments head and continues, rather than reading
the invalidated `nc` reference. This examined append path does not by itself
establish a dangling-reference bug. Broader iterator/alias lifetimes remain
for coverage mapping.

The test fixture's plugin order differs from production: containment precedes
membership in `src/test/seq_ncontains_facet.cpp:98-102`. The inspected
cross-boundary test (388-408) uses a concrete needle lowered to regex membership,
not the shared variable-width prefix from P1. The substitution/trail test
(411-435) covers a different shape. These tests are context, not executed
evidence or a claim that all test coverage was exhaustively classified.

Potential next source-grounded obligations to investigate during selection:
the separate all-determined-mismatches discharge branch (285-291), qhead and
dependency restoration across append/substitution/pop, and bounds/lifetimes
in other facets. The published candidate guard addresses only the selected
prefix-pruning model; do not extend its proof to the discharge branch.

## Remaining uncertainty

Native assertion-arrival order, all preprocessing, interactions with earlier
facets, completeness of a constraining end-to-end formula, actual solver
answer and model validation remain unverified. The finding remains a
conditional MODEL refutation with improved source correspondence. Publish
this follow-up with batch 2; retain the immutable original report/evidence.
