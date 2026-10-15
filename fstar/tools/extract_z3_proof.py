#!/usr/bin/env python3
"""
extract_z3_proof.py

Uses Z3's *Python* front-end (the `z3` module, i.e. z3py) to produce a
real proof object for a small example, pretty-prints the equational
fragment of that proof object into a JSON proof document matching
`Z3ProofJson.fst`'s schema, and (optionally) checks it by piping that
JSON straight to the precompiled, standalone native checker executable
(see `fstar/OCAML_CHECKER_REPORT.md`) -- no `fstar.exe`/SMT-solver
invocation happens in this script at all; that cost was already paid
once, at build time, by `fstar/tools/build_ocaml_checker.ps1`.

Why this works at all, and what it does NOT attempt
-----------------------------------------------------
`Z3ProofTheory.fst`'s `proof` type models only the *equational*
fragment of Z3's real proof calculus that `rewriter_def.h` produces:
`PR_REFLEXIVITY`/`PR_SYMMETRY`/`PR_TRANSITIVITY`/`PR_MONOTONICITY`/
`PR_REWRITE`/(`PR_BIND`+`PR_QUANT_INTRO`). A real `(get-proof)`/
`Solver.proof()` output for a nontrivial `check-sat` is a much bigger
DAG dominated by *inferential* rules (`PR_ASSERTED`, `PR_HYPOTHESIS`,
`PR_MODUS_PONENS`, `PR_UNIT_RESOLUTION`, `PR_TH_LEMMA`, ...) that
conclude a bare formula, not an equation -- outside this file's model
entirely (see `PROOF_JUSTIFICATIONS_REPORT.md`/
`PREPROCESSING_PROOFS_REPORT.md` for the separate files that *do*
model some of those).

So this script does two things, deliberately kept distinct:

1. Walks down from the proof's root through any wrapper nodes (e.g. a
   top-level `mp`) to find the first strictly-equational subtree --
   for the example used here (`not(not(x)) == x`, refuted by negation)
   this is *exactly* a `trans(monotonicity(rewrite ...), rewrite
   ...)` node, i.e. real Z3-internal preprocessing naturally produces
   a `Trans(Congr(f, ...), Rewrite(...))` shape that maps onto
   `Z3ProofTheory.fst`'s calculus with **no approximation at all** --
   every `rewrite` leaf encountered really is a `PR_REWRITE` leaf, every
   `monotonicity`/`transitivity` node really is exactly what `Congr`/
   `Trans` model.
2. For any node reachable *within* that subtree whose rule is outside
   the supported set (should not happen for this example, but is
   handled defensively for other inputs), falls back to representing
   it as an opaque `Rewrite` leaf: `Rewrite a b` if its own conclusion
   is itself an equation/iff `(= a b)`/`(iff a b)`, else `Rewrite F
   true_marker` for a bare formula `F` (a documented, non-semantic
   *representational* bridge -- `true_marker` is just an uninterpreted
   Bool constant, this does not assert or rely on `F` actually being
   true in any interpretation; it only lets the structural checker
   treat "this was some other kind of derivation step" uniformly as
   one more trusted leaf, exactly as `PR_REWRITE` leaves already are).

Usage:
    python extract_z3_proof.py [smt2-file] [--fast-check] [--out FILE.fst]

If `smt2-file` is omitted, a small built-in example is used instead
(`not(not(x)) == x`, refuted by negation). If given, its assertions
are parsed and checked; they must be jointly unsatisfiable (there is
no refutation proof to extract from a `sat` result).

A JSON proof document is always written (named after `--out`/
`--json-out`). With `--fast-check`, it is additionally piped to the
precompiled, standalone native checker executable (see
`fstar/OCAML_CHECKER_REPORT.md`) via WSL. This does NOT invoke
fstar.exe, does NOT write/compile any new `.fst` file, and does NOT
run the SMT solver: the executable is built once
(`fstar/tools/build_ocaml_checker.ps1`) from the extracted OCaml form
of the same Pulse-verified checker and simply interprets the JSON
directly, typically in single-digit milliseconds per proof.

`--full-proof` instead exports the complete ground refutation DAG,
including resolution, mp, congruence and hypothesis discharge. Unsupported
rules and unsupported rewrite leaves remain explicit obligations: a structurally
valid full derivation with such obligations reports PARTIAL (exit 3),
not a certified UNSAT result. The default equational mode is unchanged.
Definitional axioms are trusted by default. With --check-original-assertions,
their entire conclusions must match supplied input assertions, just like
ordinary asserted leaves. Binary commutativity for equality, Boolean and/or,
and Int addition/multiplication is checked by verified inference rules.
Identity and order-preserving n-ary Boolean and/or flattening rewrites
are discharged by the full-proof checker, along with verified Boolean
normalization and bounded Boolean equivalence. Other rewrite matches
are diagnostic.

`--emit-json-fst` additionally writes a tiny JSON-instance `.fst` file
wrapping the same JSON document, purely as an artifact for manually
cross-validating against a real `fstar.exe` invocation during
development; it is not needed for, and is not touched by,
`--fast-check`.
"""
import argparse
import json as json_mod
import os
import subprocess
import sys

import z3


# --------------------------------------------------------------------
# Z3 proof-rule kinds this script converts *faithfully* (matching
# Z3ProofTheory.fst's `proof` constructors exactly) vs. treats as
# opaque trusted leaves (everything else).
# --------------------------------------------------------------------

EQUATIONAL_KINDS = {
    z3.Z3_OP_PR_REFLEXIVITY,
    z3.Z3_OP_PR_SYMMETRY,
    z3.Z3_OP_PR_TRANSITIVITY,
    z3.Z3_OP_PR_MONOTONICITY,
    z3.Z3_OP_PR_REWRITE,
    z3.Z3_OP_PR_REWRITE_STAR,
    z3.Z3_OP_PR_QUANT_INTRO,
}

FULL_PROOF_REWRITES = {"reflexivity", "and_flatten", "or_flatten",
                       "eq_reflexive", "boolean_equiv"}


def fstar_ident(prefix, n):
    return "%s%d" % (prefix, n)


# --------------------------------------------------------------------
# Python-side mirror of `Z3PatternMatchedProofChecker.fst`'s six
# structural rewrite-rule matchers (`match_select_store_same`,
# `match_store_same_twice`, `match_store_redundant`,
# `match_concat_assoc`, `match_not_not`, `match_bvand_self`), applied
# directly to the *original* z3 ASTs (before F* conversion) so that a
# human-readable log can be produced without round-tripping through
# `fstar.exe`. This mirror is deliberately *not* trusted on its own:
# `generate()` below also emits, into the produced `.fst` file, a call
# to the real, proven `collect_unmatched` and an `assert_norm` that its
# length equals this script's own unmatched count -- if the two
# disagree (e.g. this mirror is buggy, or out of sync with the F*
# matcher library), the generated file simply fails to type-check,
# so the log's "matched"/"unmatched" classification is mechanically
# cross-checked against the verified matcher, not merely asserted by
# this script.
# --------------------------------------------------------------------

def _is_app_of(e, kind):
    return z3.is_app(e) and e.num_args() > 0 and e.decl().kind() == kind


def _boolean_flatten(s, t):
    if not (z3.is_app(s) and z3.is_app(t)
            and s.decl().kind() in (z3.Z3_OP_AND, z3.Z3_OP_OR)
            and s.decl().kind() == t.decl().kind()):
        return None
    kind = s.decl().kind()
    flat = []
    stack = list(reversed(s.children()))
    while stack:
        arg = stack.pop()
        if z3.is_app(arg) and arg.decl().kind() == kind:
            stack.extend(reversed(arg.children()))
        else:
            flat.append(arg)
    if (len(flat) == t.num_args()
            and all(a.eq(b) for a, b in zip(flat, t.children()))):
        return "and_flatten" if kind == z3.Z3_OP_AND else "or_flatten"
    return None


def classify_rewrite(s: z3.ExprRef, t: z3.ExprRef):
    """Returns the matched pattern's name (one of the fourteen below) if
       `(s, t)` fits one of `Z3PatternMatchedProofChecker.fst`'s fourteen
       schemas for *arbitrary* sub-expressions, else `None`."""
    # s = s (reflexivity): sound for any theory/sort, no theory lemma
    # needed -- see Z3PatternMatchedProofChecker.fst section 4g.
    if s.eq(t):
        return "reflexivity"
    # select(store(a,i,x),i) = x
    if (_is_app_of(s, z3.Z3_OP_SELECT) and s.num_args() == 2 and
            _is_app_of(s.arg(0), z3.Z3_OP_STORE) and s.arg(0).num_args() == 3 and
            s.arg(0).arg(1).eq(s.arg(1)) and t.eq(s.arg(0).arg(2))):
        return "select_store_same"
    # store(store(a,i,x),i,y) = store(a,i,y)
    if (_is_app_of(s, z3.Z3_OP_STORE) and s.num_args() == 3 and
            _is_app_of(s.arg(0), z3.Z3_OP_STORE) and s.arg(0).num_args() == 3 and
            _is_app_of(t, z3.Z3_OP_STORE) and t.num_args() == 3 and
            s.arg(0).arg(1).eq(s.arg(1)) and s.arg(1).eq(t.arg(1)) and
            s.arg(0).arg(0).eq(t.arg(0)) and s.arg(2).eq(t.arg(2))):
        return "store_same_twice"
    # store(a,i,select(a,i)) = a
    if (_is_app_of(s, z3.Z3_OP_STORE) and s.num_args() == 3 and
            _is_app_of(s.arg(2), z3.Z3_OP_SELECT) and s.arg(2).num_args() == 2 and
            s.arg(0).eq(s.arg(2).arg(0)) and s.arg(1).eq(s.arg(2).arg(1)) and
            t.eq(s.arg(0))):
        return "store_redundant"
    # (a++b)++c = a++(b++c)
    if (_is_app_of(s, z3.Z3_OP_SEQ_CONCAT) and s.num_args() == 2 and
            _is_app_of(s.arg(0), z3.Z3_OP_SEQ_CONCAT) and s.arg(0).num_args() == 2 and
            _is_app_of(t, z3.Z3_OP_SEQ_CONCAT) and t.num_args() == 2 and
            _is_app_of(t.arg(1), z3.Z3_OP_SEQ_CONCAT) and t.arg(1).num_args() == 2 and
            s.arg(0).arg(0).eq(t.arg(0)) and s.arg(0).arg(1).eq(t.arg(1).arg(0)) and
            s.arg(1).eq(t.arg(1).arg(1))):
        return "concat_assoc"
    # not(not(x)) = x
    if (_is_app_of(s, z3.Z3_OP_NOT) and s.num_args() == 1 and
            _is_app_of(s.arg(0), z3.Z3_OP_NOT) and s.arg(0).num_args() == 1 and
            t.eq(s.arg(0).arg(0))):
        return "not_not"
    # bvand(y,y) = y
    if (_is_app_of(s, z3.Z3_OP_BAND) and s.num_args() == 2 and
            s.arg(0).eq(s.arg(1)) and t.eq(s.arg(0))):
        return "bvand_self"
    # (= a b) = (= b a) -- symmetry of equality, any sort.
    if (_is_app_of(s, z3.Z3_OP_EQ) and s.num_args() == 2 and
            _is_app_of(t, z3.Z3_OP_EQ) and t.num_args() == 2 and
            s.arg(0).eq(t.arg(1)) and s.arg(1).eq(t.arg(0))):
        return "eq_symm"
    # select(store(a,i,x),j) = select(a,j), i <> j -- only matched when
    # `i`/`j` are themselves distinctly-*named* 0-ary uninterpreted Int
    # constants (mirrors Z3PatternMatchedProofChecker.fst's
    # `select_store_diff_leaf_ok`'s decidable, purely syntactic side
    # condition; compound index expressions are intentionally left
    # unmatched, same as the F* checker).
    if (_is_app_of(s, z3.Z3_OP_SELECT) and s.num_args() == 2 and
            _is_app_of(s.arg(0), z3.Z3_OP_STORE) and s.arg(0).num_args() == 3 and
            _is_app_of(t, z3.Z3_OP_SELECT) and t.num_args() == 2 and
            s.arg(0).arg(0).eq(t.arg(0)) and s.arg(1).eq(t.arg(1)) and
            z3.is_const(s.arg(0).arg(1)) and s.arg(0).arg(1).decl().kind() == z3.Z3_OP_UNINTERPRETED and
            z3.is_const(s.arg(1)) and s.arg(1).decl().kind() == z3.Z3_OP_UNINTERPRETED and
            s.arg(0).arg(1).decl().name() != s.arg(1).decl().name()):
        return "select_store_diff"
    # store(store(a,i,x),j,y) = store(store(a,j,y),i,x), i <> j -- the
    # index-swap twin of select_store_diff, same side condition and same
    # syntactic-distinctness restriction (mirrors
    # Z3PatternMatchedProofChecker.fst's `store_commute_leaf_ok`).
    if (_is_app_of(s, z3.Z3_OP_STORE) and s.num_args() == 3 and
            _is_app_of(s.arg(0), z3.Z3_OP_STORE) and s.arg(0).num_args() == 3 and
            _is_app_of(t, z3.Z3_OP_STORE) and t.num_args() == 3 and
            _is_app_of(t.arg(0), z3.Z3_OP_STORE) and t.arg(0).num_args() == 3 and
            s.arg(0).arg(0).eq(t.arg(0).arg(0)) and
            s.arg(0).arg(1).eq(t.arg(1)) and s.arg(1).eq(t.arg(0).arg(1)) and
            s.arg(0).arg(2).eq(t.arg(2)) and s.arg(2).eq(t.arg(0).arg(2)) and
            z3.is_const(s.arg(0).arg(1)) and s.arg(0).arg(1).decl().kind() == z3.Z3_OP_UNINTERPRETED and
            z3.is_const(s.arg(1)) and s.arg(1).decl().kind() == z3.Z3_OP_UNINTERPRETED and
            s.arg(0).arg(1).decl().name() != s.arg(1).decl().name()):
        return "store_commute"
    # An arbitrary-length chain of nested `store`s against *any*
    # reordering of the same `(index,value)` updates, provided every
    # index is a distinctly-named 0-ary uninterpreted constant --
    # mirrors Z3PatternMatchedProofChecker.fst's `store_perm_leaf_ok`
    # (§4k), the general theorem `store_commute` is the `n = 2` special
    # case of. Peels nested `store` applications off the outside of
    # each side (`flatten_store`), then checks: same base array, at
    # least two updates, equal-length chains, every index on each side
    # pairwise distinct by name, and the two update lists contain
    # exactly the same set of `(index,value)` pairs (order-independent).
    if _match_store_perm(s, t) is not None:
        return "store_perm"
    # (and p q) = (not (or (not p) (not q))) -- De Morgan for a binary
    # `and`, tolerating Z3 both commuting the `or`'s two disjuncts and
    # fusing away a resulting double negation (mirrors
    # Z3PatternMatchedProofChecker.fst's `demorgan_and_leaf_ok`/
    # `neg_in_t`).
    if (_is_app_of(s, z3.Z3_OP_AND) and s.num_args() == 2 and
            _is_app_of(t, z3.Z3_OP_NOT) and t.num_args() == 1 and
            _is_app_of(t.arg(0), z3.Z3_OP_OR) and t.arg(0).num_args() == 2):
        p, q = s.arg(0), s.arg(1)
        d1, d2 = t.arg(0).arg(0), t.arg(0).arg(1)
        if ((_neg_in_t(d1, p) and _neg_in_t(d2, q)) or
                (_neg_in_t(d1, q) and _neg_in_t(d2, p))):
            return "demorgan_and"
    # (p => q) = (not p) \/ q -- implication elimination.
    if (_is_app_of(s, z3.Z3_OP_IMPLIES) and s.num_args() == 2 and
            _is_app_of(t, z3.Z3_OP_OR) and t.num_args() == 2 and
            _is_app_of(t.arg(0), z3.Z3_OP_NOT) and t.arg(0).num_args() == 1 and
            t.arg(0).arg(0).eq(s.arg(0)) and t.arg(1).eq(s.arg(1))):
        return "implies_as_or"
    # (a = (not c)) = (not (= c a)) -- eq_symm combined with an
    # equality/disequality rearrangement for Bool-sorted a/c (mirrors
    # Z3PatternMatchedProofChecker.fst's `eq_not_leaf_ok`).
    if (_is_app_of(s, z3.Z3_OP_EQ) and s.num_args() == 2 and
            _is_app_of(s.arg(1), z3.Z3_OP_NOT) and s.arg(1).num_args() == 1 and
            _is_app_of(t, z3.Z3_OP_NOT) and t.num_args() == 1 and
            _is_app_of(t.arg(0), z3.Z3_OP_EQ) and t.arg(0).num_args() == 2 and
            t.arg(0).arg(0).eq(s.arg(1).arg(0)) and t.arg(0).arg(1).eq(s.arg(0))):
        return "eq_not"
    return None


def _neg_in_t(d: z3.ExprRef, p: z3.ExprRef) -> bool:
    """Does `d` denote the negation of `p`, either literally (`d = (not
       p)`) or, when `p` itself is `(not r)`, as the bare,
       double-negation-eliminated `r` (`d = r`)? Mirrors
       Z3PatternMatchedProofChecker.fst's `neg_in_t`."""
    if _is_app_of(d, z3.Z3_OP_NOT) and d.num_args() == 1 and d.arg(0).eq(p):
        return True
    if _is_app_of(p, z3.Z3_OP_NOT) and p.num_args() == 1 and d.eq(p.arg(0)):
        return True
    return False


def classify_full_rewrite(s: z3.ExprRef, t: z3.ExprRef):
    if s.eq(t):
        return "reflexivity"
    if z3.is_eq(s) and s.arg(0).eq(s.arg(1)) and z3.is_true(t):
        return "eq_reflexive"
    return (_boolean_flatten(s, t)
            or ("boolean_equiv" if _bounded_boolean_equiv(s, t) else None)
            or classify_rewrite(s, t))


def _bounded_boolean_equiv(s, t, depth=8, width=10):
    """Diagnostic mirror of verified structural and bounded Boolean checking."""
    if not (z3.is_bool(s) and z3.is_bool(t)):
        return False
    connectives = {z3.Z3_OP_AND, z3.Z3_OP_OR, z3.Z3_OP_NOT,
                   z3.Z3_OP_IMPLIES, z3.Z3_OP_EQ}
    constants = {z3.Z3_OP_TRUE, z3.Z3_OP_FALSE}

    def kind(e):
        if not z3.is_app(e):
            return None
        k = e.decl().kind()
        if k in constants or (k in connectives
                              and all(z3.is_bool(a) for a in e.children())):
            return k
        return None

    def nodes(e, remaining):
        k = kind(e)
        if k in constants:
            return set()
        result = {e.get_id()}
        if remaining and k is not None:
            for a in e.children():
                result.update(nodes(a, remaining - 1))
        return result

    boundaries = nodes(s, depth) & nodes(t, depth)
    atoms = {}

    def cut(e, remaining, shared):
        k = kind(e)
        if z3.is_eq(e) and e.arg(0).eq(e.arg(1)):
            return z3.Z3_OP_TRUE, []
        if e.get_id() in shared or k is None or (not remaining and k not in constants):
            return ("atom", atoms.setdefault(e.get_id(), len(atoms)))
        return (k, [cut(a, remaining - 1, shared) for a in e.children()])

    def normalize(e, negative=False):
        k, args = e
        if k == "atom":
            return (z3.Z3_OP_NOT, [e]) if negative else e
        if k in constants:
            return ((z3.Z3_OP_FALSE if k == z3.Z3_OP_TRUE else z3.Z3_OP_TRUE)
                    if negative else k, [])
        if k == z3.Z3_OP_NOT:
            return normalize(args[0], not negative)
        if k == z3.Z3_OP_EQ:
            result = (k, [normalize(a) for a in args])
            return (z3.Z3_OP_NOT, [result]) if negative else result
        if k == z3.Z3_OP_IMPLIES:
            op = z3.Z3_OP_AND if negative else z3.Z3_OP_OR
            children = [normalize(args[0], not negative), normalize(args[1], negative)]
        else:
            op = ({z3.Z3_OP_AND: z3.Z3_OP_OR, z3.Z3_OP_OR: z3.Z3_OP_AND}[k]
                  if negative else k)
            children = [normalize(a, negative) for a in args]
        joined = []
        for child in children:
            joined.extend(child[1] if child[0] == op else [child])
        unit = (z3.Z3_OP_TRUE if op == z3.Z3_OP_AND else z3.Z3_OP_FALSE, [])
        zero = (z3.Z3_OP_FALSE if op == z3.Z3_OP_AND else z3.Z3_OP_TRUE, [])
        other = z3.Z3_OP_OR if op == z3.Z3_OP_AND else z3.Z3_OP_AND

        def absorbed(x, ys):
            return x[0] == other and any(a in ys for a in x[1])

        def complementary(x, y):
            if x[0] == z3.Z3_OP_NOT:
                return x[1][0] == y
            return y[0] == z3.Z3_OP_NOT and x == y[1][0]

        reduced = []
        for x in reversed(joined):
            if x == unit:
                continue
            if x == zero or reduced == [zero] or any(complementary(x, y) for y in reduced):
                reduced = [zero]
            elif x not in reduced and not absorbed(x, reduced):
                reduced = [x] + [y for y in reduced if not absorbed(y, [x])]
        return unit if not reduced else reduced[0] if len(reduced) == 1 else (op, reduced)

    def shape_equal(a, b, fuel=32):
        if a == b:
            return True
        if not fuel or a[0] != b[0]:
            return False
        k, xs = a
        ys = b[1]
        if k == z3.Z3_OP_NOT:
            return shape_equal(xs[0], ys[0], fuel - 1)
        if k == z3.Z3_OP_EQ:
            return ((shape_equal(xs[0], ys[0], fuel - 1)
                     and shape_equal(xs[1], ys[1], fuel - 1))
                    or (shape_equal(xs[0], ys[1], fuel - 1)
                        and shape_equal(xs[1], ys[0], fuel - 1)))
        if k in (z3.Z3_OP_AND, z3.Z3_OP_OR) and fuel >= 2:
            return (all(any(shape_equal(x, y, fuel - 2) for y in ys) for x in xs)
                    and all(any(shape_equal(y, x, fuel - 2) for x in xs) for y in ys))
        return False

    def height(e):
        return (1 + max((height(a) for a in e.children()), default=0)
                if kind(e) is not None else 0)

    if shape_equal(normalize(cut(s, height(s), set())),
                   normalize(cut(t, height(t), set()))):
        return True
    atoms.clear()
    cs, ct = cut(s, depth, boundaries), cut(t, depth, boundaries)
    if shape_equal(normalize(cs), normalize(ct)):
        return True
    if len(atoms) > width:
        return False
    rows = 1 << len(atoms)
    mask = (1 << rows) - 1
    values = [sum(1 << row for row in range(rows) if row & (1 << a))
              for a in range(len(atoms))]

    def evaluate(e):
        k, args = e
        if k == "atom":
            return values[args]
        vs = [evaluate(a) for a in args]
        if k == z3.Z3_OP_TRUE:
            return mask
        if k == z3.Z3_OP_FALSE:
            return 0
        if k == z3.Z3_OP_AND:
            result = mask
            for v in vs:
                result &= v
            return result
        if k == z3.Z3_OP_OR:
            result = 0
            for v in vs:
                result |= v
            return result
        if k == z3.Z3_OP_NOT:
            return mask ^ vs[0]
        if k == z3.Z3_OP_IMPLIES:
            return (mask ^ vs[0]) | vs[1]
        if k == z3.Z3_OP_EQ:
            return mask ^ vs[0] ^ vs[1]
        raise AssertionError("Unexpected Boolean skeleton operator")

    return evaluate(cs) == evaluate(ct)


def _flatten_store(e: z3.ExprRef):
    """Peels nested `store` applications off the outside of `e`,
       returning `(base, [(index, value), ...])` with the outermost
       `store`'s pair appended last -- mirrors
       Z3PatternMatchedProofChecker.fst's `flatten_store`."""
    pairs = []
    while _is_app_of(e, z3.Z3_OP_STORE) and e.num_args() == 3:
        pairs.append((e.arg(1), e.arg(2)))
        e = e.arg(0)
    pairs.reverse()
    return e, pairs


def _is_named_uninterp_const(e: z3.ExprRef) -> bool:
    return z3.is_const(e) and e.decl().kind() == z3.Z3_OP_UNINTERPRETED


def _pairwise_distinct_keys(pairs) -> bool:
    names = []
    for (idx, _) in pairs:
        if not _is_named_uninterp_const(idx):
            return False
        names.append(idx.decl().name())
    return len(names) == len(set(names))


def _same_update_set(pairs1, pairs2) -> bool:
    def mem(p, ps):
        return any(p[0].eq(q[0]) and p[1].eq(q[1]) for q in ps)
    return (len(pairs1) == len(pairs2) and
            all(mem(p, pairs2) for p in pairs1) and
            all(mem(p, pairs1) for p in pairs2))


def _match_store_perm(s: z3.ExprRef, t: z3.ExprRef):
    base_s, us_s = _flatten_store(s)
    base_t, us_t = _flatten_store(t)
    if (base_s.eq(base_t) and len(us_s) >= 2 and len(us_s) == len(us_t) and
            _pairwise_distinct_keys(us_s) and _pairwise_distinct_keys(us_t) and
            _same_update_set(us_s, us_t)):
        return (base_s, us_s, us_t)
    return None


class Converter:
    def __init__(self):
        self.sort_lines = []
        self.decl_lines = []
        self.expr_lines = []
        self.proof_lines = []
        self.sort_cache = {}   # Z3 sort identity -> ident
        self.decl_cache = {}   # (Z3 declaration identity, application arity) -> ident
        self.expr_cache = {}   # z3 ast id -> ident
        self.proof_cache = {}  # z3 ast id -> ident
        # JSON-parallel node pools (see Z3ProofJson.fst's doc comment for the
        # schema). Each list's *index* is exactly the integer every
        # "<prefix>_N" F*-identifier above already encodes in its own name
        # (`_idx` below just extracts that N), so no separate bookkeeping is
        # needed to keep the two representations' node numbering in sync --
        # they are emitted from the very same call sites, one node at a time.
        self.sort_json = []
        self.decl_json = []
        self.expr_json = []
        self.proof_json = []
        self.true_marker_emitted = False
        self.rewrite_log = []  # list of (s:ExprRef, t:ExprRef, matched_name:str|None)

    @staticmethod
    def _idx(ident: str) -> int:
        return int(ident.rsplit("_", 1)[1])

    # ---- sorts -----------------------------------------------------
    # Z3InterpretedProofChecker.fst's six interpreted ops are tied to
    # specific, literal sort names (`int_s = BaseSort "Int"`, `bool_s =
    # BaseSort "Bool"`, `bv_s = BaseSort "BV32"`, `seq_s = BaseSort
    # "SeqInt"`, `arr_s = ArraySort [int_s] int_s`). `z3.SortRef.name()`
    # already agrees for Int/Bool/Array, but reports plain "bv"/"Seq"
    # for bit-vector/sequence sorts (losing the width/element type), so
    # those two are special-cased here to the exact literal strings
    # the matcher library expects -- purely a naming fix, changing
    # nothing semantic.
    def sort(self, s: z3.SortRef) -> str:
        key = s.get_id()
        if s.kind() == z3.Z3_BV_SORT:
            name = "BV%d" % s.size()
        elif s.kind() == z3.Z3_SEQ_SORT and s.basis().kind() == z3.Z3_INT_SORT:
            name = "SeqInt"
        else:
            name = s.name()
        if key in self.sort_cache:
            return self.sort_cache[key]
        if s.kind() == z3.Z3_ARRAY_SORT:
            # Multi-argument arrays expose `domain_n(i)` but not a
            # Python-level `arity()`; the arity itself has to come from
            # the raw C API (`Z3_get_array_arity`) instead. Computed
            # *before* `ident` below: this recurses into `self.sort()`
            # for the domain/range sorts, which can itself grow
            # `self.sort_cache` (e.g. for `Array(Int,Int)`, discovering
            # and interning the shared `Int` sort) -- `ident` must be
            # allocated only once that settles, or it can collide with
            # an identifier a nested recursive call already claimed.
            arity = z3.z3core.Z3_get_array_arity(s.ctx_ref(), s.ast)
            dom = [self.sort(s.domain_n(i)) for i in range(arity)]
            rng = self.sort(s.range())
            ident = fstar_ident("srt_", len(self.sort_cache))
            self.sort_lines.append(
                "let %s : sort = ArraySort [%s] %s" % (ident, "; ".join(dom), rng)
            )
            self.sort_json.append({"kind": "array", "dom": [self._idx(d) for d in dom], "rng": self._idx(rng)})
        else:
            ident = fstar_ident("srt_", len(self.sort_cache))
            self.sort_lines.append('let %s : sort = BaseSort "%s"' % (ident, name))
            self.sort_json.append({"kind": "base", "name": name})
        self.sort_cache[key] = ident
        return ident

    def mk_array_sort(self, dom_idents, rng_ident):
        """Register a *new* array sort directly from already-interned
           domain/range idents, for the one case (a `lambda`'s own
           `qsort`) that does not go through a `z3.SortRef` -- see
           `expr()`'s `Quantifier`/`Lambda_k` case below. Never deduped
           against `sort_cache` (two structurally-identical lambda
           qsorts simply get two separate entries); this is a strict
           behavioral no-op versus the prior code, which inlined a
           fresh, equally undeduped literal every time instead."""
        ident = fstar_ident("srt_", len(self.sort_cache))
        self.sort_lines.append(
            "let %s : sort = ArraySort [%s] %s" % (ident, "; ".join(dom_idents), rng_ident)
        )
        self.sort_json.append(
            {"kind": "array", "dom": [self._idx(d) for d in dom_idents], "rng": self._idx(rng_ident)}
        )
        self.sort_cache[ident] = ident
        return ident

    # ---- func_decls ----------------------------------------------------
    # `fact`/`check_proof` never consult `interp`/`domain`, only
    # `decl_name`+structural shape, so leaving every func_decl
    # uninterpreted (`interp = None`) is a faithful simplification for
    # *those*. But `Z3PatternMatchedProofChecker.fst`'s rewrite-rule
    # matchers additionally require the specific interpreted tag
    # (`op_not`/`op_select`/`op_store`/`op_bvand`/`op_concat`/`op_eq`)
    # to be set before they will recognize a leaf's shape at all
    # (`decl_shape_ok`), so any z3 declaration whose kind is one of
    # those seven ops, applied at the arity that op expects, is tagged
    # accordingly here -- every other declaration (including `op_plus`,
    # not needed by any matcher) stays `None`, so `decl_shape_ok`'s
    # `None -> true` case covers it with no change in behavior.
    def func_decl(self, d: z3.FuncDeclRef, arity: int) -> str:
        key = (d.get_id(), arity)
        if key in self.decl_cache:
            return self.decl_cache[key]
        ident = fstar_ident("fd_", len(self.decl_cache))
        dom = [self.sort(d.domain(i)) for i in range(arity)]
        rng = self.sort(d.range())
        tag = None
        kind = d.kind()
        if kind == z3.Z3_OP_NOT and arity == 1:
            tag = "op_not"
        elif kind == z3.Z3_OP_SELECT and arity == 2:
            tag = "op_select"
        elif kind == z3.Z3_OP_STORE and arity == 3:
            tag = "op_store"
        elif kind == z3.Z3_OP_BAND and arity == 2:
            tag = "op_bvand"
        elif kind == z3.Z3_OP_SEQ_CONCAT and arity == 2:
            tag = "op_concat"
        elif kind == z3.Z3_OP_EQ and arity == 2:
            tag = "op_eq"
        elif kind == z3.Z3_OP_AND and arity == 2:
            tag = "op_and"
        elif kind == z3.Z3_OP_OR and arity == 2:
            tag = "op_or"
        elif kind == z3.Z3_OP_IMPLIES and arity == 2:
            tag = "op_implies"
        interp = ("Some %s" % tag) if tag is not None else "None"
        self.decl_lines.append(
            'let %s : func_decl = { decl_name = "%s"; domain = [%s]; range = %s; '
            'interp = %s; int_params = [] }'
            % (ident, d.name(), "; ".join(dom), rng, interp)
        )
        self.decl_json.append({
            "name": d.name(),
            "domain": [self._idx(s) for s in dom],
            "range": self._idx(rng),
            "interp": tag,
            "int_params": [],
        })
        self.decl_cache[key] = ident
        return ident

    def true_marker(self) -> str:
        if not self.true_marker_emitted:
            bool_s = self.sort(z3.BoolSort())
            # Assigned through the same numeric `fd_N` sequence/cache as
            # every other declaration (keyed under a key no real z3
            # FuncDeclRef can ever produce) purely so its JSON array
            # position matches its ident's trailing number, exactly like
            # every other declaration -- `_idx` below relies on that.
            ident = fstar_ident("fd_", len(self.decl_cache))
            self.decl_lines.append(
                'let %s : func_decl = '
                '{ decl_name = "true_marker"; domain = []; range = %s; '
                'interp = None; int_params = [] }' % (ident, bool_s)
            )
            self.decl_json.append({
                "name": "true_marker", "domain": [], "range": self._idx(bool_s),
                "interp": None, "int_params": [],
            })
            self.decl_cache[("__true_marker__", 0)] = ident
            self.true_marker_emitted = True
        return self.decl_cache[("__true_marker__", 0)]

    # ---- expressions -------------------------------------------------
    def expr(self, e: z3.ExprRef) -> str:
        key = e.get_id()
        if key in self.expr_cache:
            return self.expr_cache[key]
        if z3.is_quantifier(e):
            bound_sorts = [self.sort(e.var_sort(i)) for i in range(e.num_vars())]
            body = self.expr(e.body())
            if e.is_lambda():
                qk = "Lambda_k"
                qk_json = "lambda"
                body_sort = self.sort(e.body().sort())
                qsort = self.mk_array_sort(bound_sorts, body_sort)
            else:
                qk = "Forall_k" if e.is_forall() else "Exists_k"
                qk_json = "forall" if e.is_forall() else "exists"
                qsort = self.sort(z3.BoolSort())
            ident = fstar_ident("e_", len(self.expr_cache))
            self.expr_lines.append(
                "let %s : expr = Quantifier %s [%s] %s %s"
                % (ident, qk, "; ".join(bound_sorts), qsort, body)
            )
            self.expr_json.append({
                "kind": "quant", "qk": qk_json,
                "bound_sorts": [self._idx(s) for s in bound_sorts],
                "qsort": self._idx(qsort), "body": self._idx(body),
            })
        elif z3.is_var(e):
            idx = z3.get_var_index(e)
            s = self.sort(e.sort())
            ident = fstar_ident("e_", len(self.expr_cache))
            self.expr_lines.append("let %s : expr = Var %d %s" % (ident, idx, s))
            self.expr_json.append({"kind": "var", "idx": idx, "sort": self._idx(s)})
        else:
            args = [self.expr(e.arg(i)) for i in range(e.num_args())]
            d = self.func_decl(e.decl(), e.num_args())
            ident = fstar_ident("e_", len(self.expr_cache))
            self.expr_lines.append(
                "let %s : expr = App %s [%s]" % (ident, d, "; ".join(args))
            )
            self.expr_json.append({
                "kind": "app", "decl": self._idx(d), "args": [self._idx(a) for a in args],
            })
        self.expr_cache[key] = ident
        return ident

    # ---- proofs --------------------------------------------------------
    def opaque_leaf(self, p: z3.ExprRef) -> str:
        """Fallback for any proof node outside the equational fragment:
           if its own conclusion is an equation/iff, transcribe it
           faithfully as a `Rewrite` leaf; otherwise bridge the bare
           formula `F` to `Rewrite F true_marker` (see module docstring)."""
        concl = p.arg(p.num_args() - 1)
        if z3.is_eq(concl) or (z3.is_app(concl) and concl.decl().kind() == z3.Z3_OP_IFF):
            s_ast, t_ast = concl.arg(0), concl.arg(1)
            self.rewrite_log.append((s_ast, t_ast, classify_rewrite(s_ast, t_ast)))
            s = self.expr(s_ast)
            t = self.expr(t_ast)
        else:
            # A bare formula bridged via `true_marker`: never fits any
            # of the six equational schemas, so it is always logged as
            # unmatched (there is no lemma library for "this was some
            # other, non-equational derivation step").
            self.rewrite_log.append((concl, None, None))
            s = self.expr(concl)
            fd = self.true_marker()
            t_ident = fstar_ident("e_", len(self.expr_cache))
            self.expr_lines.append("let %s : expr = App %s []" % (t_ident, fd))
            self.expr_json.append({"kind": "app", "decl": self._idx(fd), "args": []})
            t = t_ident
        ident = fstar_ident("p_", len(self.proof_cache))
        self.proof_lines.append("let %s : proof = Rewrite %s %s" % (ident, s, t))
        self.proof_json.append({"kind": "rewrite", "s": self._idx(s), "t": self._idx(t)})
        return ident

    def proof(self, p: z3.ExprRef, depth=0, max_depth=200) -> str:
        key = p.get_id()
        if key in self.proof_cache:
            return self.proof_cache[key]
        if depth > max_depth:
            ident = self.opaque_leaf(p)
            self.proof_cache[key] = ident
            return ident
        kind = p.decl().kind()
        n = p.num_args()
        premises = [p.arg(i) for i in range(n - 1)]
        concl = p.arg(n - 1)

        if kind == z3.Z3_OP_PR_REFLEXIVITY:
            e = self.expr(concl.arg(0))
            ident = fstar_ident("p_", len(self.proof_cache))
            self.proof_lines.append("let %s : proof = Refl %s" % (ident, e))
            self.proof_json.append({"kind": "refl", "e": self._idx(e)})
        elif kind == z3.Z3_OP_PR_SYMMETRY:
            p1 = self.proof(premises[0], depth + 1, max_depth)
            ident = fstar_ident("p_", len(self.proof_cache))
            self.proof_lines.append("let %s : proof = Sym %s" % (ident, p1))
            self.proof_json.append({"kind": "sym", "p": self._idx(p1)})
        elif kind in (z3.Z3_OP_PR_TRANSITIVITY, z3.Z3_OP_PR_TRANSITIVITY_STAR) and len(premises) == 2:
            p1 = self.proof(premises[0], depth + 1, max_depth)
            p2 = self.proof(premises[1], depth + 1, max_depth)
            ident = fstar_ident("p_", len(self.proof_cache))
            self.proof_lines.append("let %s : proof = Trans %s %s" % (ident, p1, p2))
            self.proof_json.append({"kind": "trans", "p1": self._idx(p1), "p2": self._idx(p2)})
        elif kind == z3.Z3_OP_PR_MONOTONICITY:
            lhs, rhs = concl.arg(0), concl.arg(1)
            f = self.func_decl(lhs.decl(), lhs.num_args())
            args1 = [self.expr(lhs.arg(i)) for i in range(lhs.num_args())]
            args2 = [self.expr(rhs.arg(i)) for i in range(rhs.num_args())]
            prfs = [self.proof(pr, depth + 1, max_depth) for pr in premises]
            ident = fstar_ident("p_", len(self.proof_cache))
            self.proof_lines.append(
                "let %s : proof = Congr %s [%s] [%s] [%s]"
                % (ident, f, "; ".join(args1), "; ".join(args2), "; ".join(prfs))
            )
            self.proof_json.append({
                "kind": "congr", "decl": self._idx(f),
                "args1": [self._idx(a) for a in args1],
                "args2": [self._idx(a) for a in args2],
                "prfs": [self._idx(pr) for pr in prfs],
            })
        elif kind in (z3.Z3_OP_PR_REWRITE, z3.Z3_OP_PR_REWRITE_STAR):
            s_ast, t_ast = concl.arg(0), concl.arg(1)
            self.rewrite_log.append((s_ast, t_ast, classify_rewrite(s_ast, t_ast)))
            s = self.expr(s_ast)
            t = self.expr(t_ast)
            ident = fstar_ident("p_", len(self.proof_cache))
            self.proof_lines.append("let %s : proof = Rewrite %s %s" % (ident, s, t))
            self.proof_json.append({"kind": "rewrite", "s": self._idx(s), "t": self._idx(t)})
        elif kind == z3.Z3_OP_PR_QUANT_INTRO:
            q1 = concl.arg(0)
            bound_sorts = [self.sort(q1.var_sort(i)) for i in range(q1.num_vars())]
            qk = "Forall_k" if q1.is_forall() else "Exists_k"
            p1 = self.proof(premises[0], depth + 1, max_depth)
            ident = fstar_ident("p_", len(self.proof_cache))
            self.proof_lines.append(
                "let %s : proof = QuantIntro %s [%s] %s"
                % (ident, qk, "; ".join(bound_sorts), p1)
            )
            self.proof_json.append({
                "kind": "quant_intro", "qk": "forall" if q1.is_forall() else "exists",
                "bound_sorts": [self._idx(s) for s in bound_sorts],
                "p": self._idx(p1),
            })
        else:
            ident = self.opaque_leaf(p)
        self.proof_cache[key] = ident
        return ident


def find_equational_root(p: z3.ExprRef, max_depth=50):
    """Walk down from the real proof's root, through any wrapper nodes
       (mp/unit-resolution/hypothesis/asserted/...), to the first
       descendant whose own rule is in `EQUATIONAL_KINDS` -- i.e. the
       first point where the proof is *purely* an equational
       (rewriter-calculus) derivation, which is what
       `Z3ProofTheory.fst`'s `proof` type models."""
    stack = [(p, 0)]
    seen = set()
    while stack:
        node, d = stack.pop(0)
        key = node.get_id()
        if key in seen or d > max_depth:
            continue
        seen.add(key)
        if z3.is_app(node) and node.num_args() > 0:
            try:
                kind = node.decl().kind()
            except z3.Z3Exception:
                continue
            if kind in EQUATIONAL_KINDS:
                return node
            for i in range(node.num_args()):
                stack.append((node.arg(i), d + 1))
    return None


class ResolutionConverter(Converter):
    """Export the complete ground proof DAG without erasing derived facts."""

    SUPPORTED_RULES = {
        "asserted", "hypothesis", "lemma", "mp", "mp~", "unit-resolution",
        "and-elim", "not-or-elim", "iff-true", "iff-false", "iff~",
        "refl", "reflexivity", "symm", "trans", "trans*", "monotonicity", "rewrite",
        "def-axiom", "commutativity",
    }

    def __init__(self):
        super().__init__()
        self.trusted_log = []
        self.checked_theory_log = []

    def func_decl(self, d: z3.FuncDeclRef, arity: int) -> str:
        if d.kind() == z3.Z3_OP_OEQ and (
                arity != 2 or any(d.domain(i).kind() != z3.Z3_BOOL_SORT for i in range(arity))):
            raise ValueError("Full-proof mode requires Boolean observational equality")
        ident = super().func_decl(d, arity)
        tags = {
            z3.Z3_OP_TRUE: "op_true",
            z3.Z3_OP_FALSE: "op_false",
            z3.Z3_OP_AND: "op_and",
            z3.Z3_OP_OR: "op_or",
            z3.Z3_OP_OEQ: "op_oeq",
            z3.Z3_OP_ARRAY_EXT: "op_array_ext",
        }
        if (arity == 2 and d.range().kind() == z3.Z3_INT_SORT
                and all(d.domain(i).kind() == z3.Z3_INT_SORT for i in range(arity))):
            tags.update({z3.Z3_OP_ADD: "op_plus", z3.Z3_OP_MUL: "op_mul"})
        if d.kind() in tags:
            self.decl_json[self._idx(ident)]["interp"] = tags[d.kind()]
        return ident

    def proof(self, root: z3.ExprRef) -> str:
        stack = [(root, False)]
        scheduled = set()
        while stack:
            node, ready = stack.pop()
            key = node.get_id()
            if key in self.proof_cache:
                continue
            premises = [
                child for child in node.children()
                if child.sort().kind() == 1000
            ]
            if not ready:
                if key in scheduled:
                    continue
                scheduled.add(key)
                stack.append((node, True))
                stack.extend((child, False) for child in reversed(premises))
                continue
            conclusion = node.arg(node.num_args() - 1)
            if not z3.is_bool(conclusion):
                raise ValueError("Full-proof mode requires Boolean conclusions: %s"
                                 % node.decl().name())
            rule = str(node.decl().name())
            kind = rule if rule in self.SUPPORTED_RULES else "trusted"
            if rule == "commutativity" and not supported_commutativity(conclusion):
                kind = "trusted"
            entry = {
                "kind": kind,
                "conclusion": self._idx(self.expr(conclusion)),
                "premises": [self._idx(self.proof_cache[p.get_id()])
                             for p in premises],
            }
            if kind == "trusted":
                entry["rule"] = rule
                schema = (classify_array_lemma(conclusion)
                          if rule == "th-lemma" and not premises else None)
                if schema:
                    self.checked_theory_log.append((rule, conclusion, schema))
                else:
                    self.trusted_log.append((rule, conclusion))
            elif kind == "rewrite":
                self.rewrite_log.append((
                    conclusion.arg(0), conclusion.arg(1),
                    classify_full_rewrite(conclusion.arg(0), conclusion.arg(1)),
                ))
            ident = fstar_ident("rp_", len(self.proof_json))
            self.proof_cache[key] = ident
            self.proof_json.append(entry)
        return self.proof_cache[root.get_id()]


def supported_commutativity(conclusion: z3.ExprRef) -> bool:
    if not z3.is_eq(conclusion):
        return False
    a, b = conclusion.children()
    if not (z3.is_app(a) and z3.is_app(b)
            and a.num_args() == b.num_args() == 2 and a.decl().eq(b.decl())
            and a.arg(0).eq(b.arg(1)) and a.arg(1).eq(b.arg(0))):
        return False
    kind = a.decl().kind()
    return (kind in (z3.Z3_OP_EQ, z3.Z3_OP_AND, z3.Z3_OP_OR)
            or (kind in (z3.Z3_OP_ADD, z3.Z3_OP_MUL) and z3.is_int(a)))


def classify_array_lemma(conclusion: z3.ExprRef):
    """Diagnostic mirror of Z3ArrayLemma; the native checker is authoritative."""
    def flat_scalar_array(a):
        sort = a.sort()
        return (sort.kind() == z3.Z3_ARRAY_SORT
                and sort.domain().kind() not in (z3.Z3_ARRAY_SORT, z3.Z3_BOOL_SORT)
                and sort.range().kind() not in (z3.Z3_ARRAY_SORT, z3.Z3_BOOL_SORT))

    def read(e):
        return (e.children() if z3.is_select(e) and e.num_args() == 2
                and flat_scalar_array(e.arg(0)) else None)

    def write(e):
        return (e.children() if z3.is_store(e) and e.num_args() == 3
                and flat_scalar_array(e.arg(0)) else None)

    def pair(a, b, x, y):
        return (a.eq(x) and b.eq(y)) or (a.eq(y) and b.eq(x))

    def same(a, b):
        selected = read(a)
        stored = write(selected[0]) if selected else None
        return stored is not None and selected[1].eq(stored[1]) and b.eq(stored[2])

    def other(guard, a, b):
        left, right = read(a), read(b)
        stored = write(left[0]) if left else None
        return (z3.is_eq(guard) and stored is not None and right is not None
                and stored[0].eq(right[0]) and left[1].eq(right[1])
                and pair(guard.arg(0), guard.arg(1), stored[1], left[1]))

    def ext(a, b, x, y):
        left, right = read(x), read(y)
        if not (left and right and a.eq(left[0]) and b.eq(right[0])
                and left[1].eq(right[1])):
            return False
        index = left[1]
        return (z3.is_app(index) and index.decl().kind() == z3.Z3_OP_ARRAY_EXT
                and index.num_args() == 2
                and pair(index.arg(0), index.arg(1), a, b))

    def clause(p, q):
        if z3.is_eq(q):
            a, b = q.children()
            if other(p, a, b) or other(p, b, a):
                return "array_read_over_write_other"
        elif z3.is_eq(p) and z3.is_not(q) and z3.is_eq(q.arg(0)):
            a, b = p.children()
            x, y = q.arg(0).children()
            if ext(a, b, x, y) or ext(b, a, x, y):
                return "array_extensionality"
        return None

    if z3.is_eq(conclusion):
        a, b = conclusion.children()
        return "array_read_over_write_same" if same(a, b) or same(b, a) else None
    if z3.is_or(conclusion) and conclusion.num_args() == 2:
        p, q = conclusion.children()
        return clause(p, q) or clause(q, p)
    return None


def build_resolution_doc(conv: ResolutionConverter, root_ident: str, assertions,
                         check_original_assertions=False) -> dict:
    assertion_ids = [conv._idx(conv.expr(a)) for a in assertions]
    return {
        "format": "resolution-v1",
        "sorts": conv.sort_json,
        "decls": conv.decl_json,
        "exprs": conv.expr_json,
        "proofs": conv.proof_json,
        "root": conv._idx(root_ident),
        "assertions": assertion_ids,
        "check_original_assertions": check_original_assertions,
    }


# NOTE: FSTAR_HEADER/generate() below produce the full hand-written-F*-
# syntax `.fst` form of an extracted proof, checked by directly
# invoking fstar.exe. This script's own CLI (`main()`) no longer uses
# either of these: it relies solely on the JSON document + the
# precompiled standalone checker executable (`--fast-check`, see
# `fstar/OCAML_CHECKER_REPORT.md`). They are kept here because
# `tools/run_benchmarks.py` imports and calls them directly -- that
# harness's whole methodology is to *measure* fstar.exe's per-proof
# wall-clock verification time (see `QF_AX_QF_UF_BENCHMARK_REPORT.md`),
# so it genuinely needs the real fstar.exe-checked path, unlike this
# script's own default workflow.
FSTAR_HEADER = """(*
   %(module_name)s.fst -- AUTO-GENERATED by tools/extract_z3_proof.py

   This file is NOT hand-written: it is a literal transcription of a
   real proof object Z3 itself produced (via the Python front-end,
   `z3.Solver.proof()`) for the example recorded below, converted into
   `Z3ProofTheory.fst`'s `proof`/`Z3AstTheory.fst`'s `expr` syntax by
   `tools/extract_z3_proof.py`. Regenerate it by rerunning that script;
   do not hand-edit.

   Example: %(example_desc)s
*)
module %(module_name)s
#lang-pulse
open Pulse.Lib.Pervasives
open Z3AstTheory
open Z3ValueTheory
open Z3ProofTheory
open Z3PulseProofChecker
open Z3InterpretedProofChecker
open Z3PatternMatchedProofChecker

"""


def generate(module_name, example_desc, conv: Converter, root_ident: str, unmatched_count: int) -> str:
    out = [FSTAR_HEADER % {"module_name": module_name, "example_desc": example_desc}]
    out.extend(conv.sort_lines)
    out.append("")
    out.extend(conv.decl_lines)
    out.append("")
    out.extend(conv.expr_lines)
    out.append("")
    out.extend(conv.proof_lines)
    out.append("")
    out.append("let extracted_proof : proof = %s" % root_ident)
    out.append("")
    out.append(
        "(* The checker does not merely accept `extracted_proof` -- it computes\n"
        "   its exact conclusion via `fact`, which we also print/assert here.\n"
        "   Larger extracted proofs can need more SMT budget than F*'s\n"
        "   defaults to unfold the structural `fact`/`congr_matched`\n"
        "   recursion all the way down, so we bump both here. *)"
    )
    out.append("#push-options \"--z3rlimit 60 --fuel 4 --ifuel 4\"")
    out.append(
        "let lemma_extracted_proof_wellformed ()\n"
        "  : Lemma (Some? (fact extracted_proof))\n"
        "  = assert_norm (Some? (fact extracted_proof))"
    )
    out.append("")
    out.append("fn check_extracted ()")
    out.append("  requires emp")
    out.append("  ensures emp")
    out.append("{")
    out.append("  lemma_extracted_proof_wellformed ();")
    out.append("  let mut ctr = 0;")
    out.append("  let o = check_proof extracted_proof ctr;")
    out.append("  let n = !ctr;")
    out.append("  assert (pure (n == proof_size extracted_proof));")
    out.append("  assert (pure (Some? o));")
    out.append("  let ok = checker_accepts extracted_proof;")
    out.append("  assert (pure (ok == true));")
    out.append("}")
    out.append("#pop-options")
    out.append("")
    out.append(
        "(* Pattern-matching cross-check: `collect_unmatched` (already proven\n"
        "   sound -- `lemma_partial_proof_true` in\n"
        "   Z3PatternMatchedProofChecker.fst) is the trusted, independent\n"
        "   source of truth for which `Rewrite` leaves of this extracted proof\n"
        "   fit one of the six verified rewrite-rule schemas; `tools/\n"
        "   extract_z3_proof.py` separately mirrors the same six matchers in\n"
        "   Python purely to produce a human-readable log (see the\n"
        "   --log output / *.unmatched.log). This assertion forces F* to\n"
        "   recompute `collect_unmatched` on the *real* checker and confirms\n"
        "   its leftover count agrees with the Python log's count -- if the\n"
        "   Python mirror were ever wrong or out of sync with the verified\n"
        "   matcher library, this assertion (not just the log) would fail to\n"
        "   type-check. *)"
    )
    out.append("#push-options \"--z3rlimit 60 --fuel 4 --ifuel 4\"")
    out.append(
        "let lemma_unmatched_count_cross_checked ()\n"
        "  : Lemma (FStar.List.Tot.length (collect_unmatched extracted_proof) == %d)\n"
        "  = assert_norm (FStar.List.Tot.length (collect_unmatched extracted_proof) == %d)"
        % (unmatched_count, unmatched_count)
    )
    out.append("#pop-options")
    out.append("")
    return "\n".join(out)


def build_proof_doc(conv: Converter, root_ident: str, unmatched_count: int) -> dict:
    """Assemble the top-level JSON document (see `Z3ProofJson.fst`'s
       module docstring for the exact schema) from a `Converter`'s
       already-populated `*_json` node pools. `root` is just
       `Converter._idx(root_ident)` -- the root proof node's position
       in `proof_json`, exactly like every other cross-array index in
       this schema."""
    return {
        "sorts": conv.sort_json,
        "decls": conv.decl_json,
        "exprs": conv.expr_json,
        "proofs": conv.proof_json,
        "root": conv._idx(root_ident),
        "unmatched_count": unmatched_count,
    }


JSON_INSTANCE_HEADER = """(*
   %(module_name)s.fst -- AUTO-GENERATED by tools/extract_z3_proof.py --json

   Unlike the full-source `.fst` files this script can also generate
   (see `generate()`/`FSTAR_HEADER` above), this file does NOT spell
   the extracted proof out as F* syntax at all: it is just one JSON
   *string* literal plus a couple of calls into the already-compiled
   `Z3ProofJson`/`Z3PulseProofCheckerJson` checker library. The intent
   is that library's dependency stack (`Z3AstTheory`/`Z3ValueTheory`/
   `Z3ProofTheory`/`Z3InterpretedProofChecker`/
   `Z3PatternMatchedProofChecker`/`Z3PulseProofChecker`/`Z3ProofJson`/
   `Z3PulseProofCheckerJson`) is compiled exactly once and its
   `.checked` files never need to change from one proof to the next;
   each new proof only costs F* one string-constant elaboration plus
   one function call, not a fresh multi-hundred-`let`-binding term
   tree. Regenerate by rerunning the script; do not hand-edit.

   Example: %(example_desc)s
*)
module %(module_name)s
#lang-pulse
open Pulse.Lib.Pervasives
open Z3ProofJson
open Z3PulseProofCheckerJson

"""


def fstar_string_literal(s: str) -> str:
    """Escape a Python string for embedding as an F* string literal.
       F* string syntax only needs `\\\\` and `\\"` escaped (the JSON
       payload itself already carries its *own* `\\"`/`\\\\` escapes for
       its nested string fields -- this is the outer, second layer of
       escaping needed because the whole JSON document is itself being
       embedded as one F* string)."""
    return s.replace("\\", "\\\\").replace('"', '\\"')


def generate_json_instance(module_name: str, example_desc: str, doc: dict) -> str:
    payload = json_mod.dumps(doc, separators=(",", ":"))
    out = [JSON_INSTANCE_HEADER % {"module_name": module_name, "example_desc": example_desc}]
    out.append('let proof_json : string = "%s"' % fstar_string_literal(payload))
    out.append("")
    out.append(
        "(* `lemma_proof_json_sound`/`lemma_proof_json_partial_sound`\n"
        "   (Z3PulseProofCheckerJson.fst) are the pure corollaries that make\n"
        "   this assertion meaningful: if it type-checks, the JSON above both\n"
        "   parses to a well-formed proof *and* every one of its `Rewrite`\n"
        "   leaves matched a verified lemma in `Z3PatternMatchedProofChecker\n"
        "   .fst` (the strict, `all_matched` reading -- use\n"
        "   `check_proof_json_wf`/`lemma_proof_json_partial_sound` instead for\n"
        "   proofs with leftover unmatched leaves, in the \"partial\" checker\n"
        "   mode used elsewhere in this project). *)"
    )
    out.append("#push-options \"--z3rlimit 60 --fuel 4 --ifuel 4\"")
    out.append(
        "let lemma_proof_json_wellformed ()\n"
        "  : Lemma (check_proof_json_wf proof_json)\n"
        "  = assert_norm (check_proof_json_wf proof_json)"
    )
    out.append("")
    out.append("fn check_extracted ()")
    out.append("  requires emp")
    out.append("  ensures emp")
    out.append("{")
    out.append("  lemma_proof_json_wellformed ();")
    out.append("  let ok = check_proof_json proof_json;")
    out.append("  assert (pure (ok == true));")
    out.append("}")
    out.append("#pop-options")
    out.append("")
    return "\n".join(out)


def build_example():
    """`not(not(x)) == x`, refuted by negating it (`Xor`), with proof
       production enabled -- see module docstring for why Z3's real
       proof for this tautology lands exactly in the equational
       fragment this project's F* model covers."""
    z3.set_param("proof", True)
    x = z3.Bool("x")
    s = z3.Solver()
    s.add(z3.Xor(z3.Not(z3.Not(x)), x))
    result = s.check()
    assert result == z3.unsat, "example is expected to be unsat (the original formula is valid)"
    return "not(not(x)) == x  (via Xor refutation)", s.proof()


def build_from_file(path: str):
    """Elaborate a real proof object from an arbitrary `.smt2` file: parse
       its assertions with z3py, check satisfiability with proof
       production enabled, and return the resulting proof object.
       Requires the file's assertions to be jointly unsatisfiable (a
       `check-sat`/`(get-proof)` pair only makes sense for a refutation
       -- a `sat` result has no proof to extract)."""
    z3.set_param("proof", True)
    s = z3.Solver()
    s.add(z3.parse_smt2_file(path))
    result = s.check()
    if result != z3.unsat:
        raise SystemExit(
            "%s: check-sat returned %s, not unsat -- no refutation proof exists to extract"
            % (path, result)
        )
    return "assertions from %s" % path, s.proof()


def to_wsl_path(windows_path: str) -> str:
    """Converts an absolute Windows path (e.g. C:\\foo\\bar.json) into the
    corresponding /mnt/c/... path WSL sees the same file under."""
    abspath = os.path.abspath(windows_path)
    drive, rest = os.path.splitdrive(abspath)
    drive_letter = drive.rstrip(":").lower()
    rest = rest.replace("\\", "/").lstrip("/")
    return "/mnt/%s/%s" % (drive_letter, rest)


def run_fast_check(checker_exe: str, json_out: str) -> str:
    """Runs the precompiled standalone checker executable (built by
    fstar/tools/build_ocaml_checker.ps1) inside WSL against an already-
    written JSON proof document, with no fstar.exe/SMT-solver involved.
    Distinguishes checked proofs, conditional proofs, and rejection."""
    wsl_json_path = to_wsl_path(json_out)
    cmd = ["wsl", "-e", "bash", "-c",
           "%s %s" % (checker_exe, wsl_json_path)]
    res = subprocess.run(cmd, capture_output=True, text=True)
    out = res.stdout.strip()
    print(out)
    if res.stderr.strip():
        print(res.stderr.strip(), file=sys.stderr)
    if res.returncode == 0 and out == "ACCEPT":
        return "accept"
    if res.returncode == 3 and out.startswith("PARTIAL "):
        return "partial"
    return "reject"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("smt2_file", nargs="?", default=None,
                     help="path to an .smt2 file whose assertions are jointly "
                          "unsatisfiable; if omitted, uses the built-in "
                          "not(not(x)) == x example")
    ap.add_argument("--out", default="Z3ExtractedProof.fst")
    ap.add_argument("--log", default=None,
                     help="path to write the rewrite-rule matching log "
                          "(default: <out>.unmatched.log)")
    ap.add_argument("--fast-check", action="store_true",
                     help="pipe the generated JSON proof doc to the precompiled "
                          "native checker executable via WSL -- the only checking "
                          "path this script invokes; never writes or compiles a "
                          ".fst file for the check itself")
    ap.add_argument("--checker-exe", default="~/z3checker/checker",
                     help="path (inside WSL) to the compiled checker executable built by "
                          "fstar/tools/build_ocaml_checker.ps1")
    ap.add_argument("--json-out", default=None,
                     help="path for the JSON proof document (default: <out>.json)")
    ap.add_argument("--full-proof", action="store_true",
                     help="export/check the complete ground refutation, including "
                          "resolution, mp, hypothesis discharge and congruence; "
                          "report unverified leaves as explicit obligations")
    ap.add_argument("--check-original-assertions", action="store_true",
                     help="with --full-proof, require entire def-axiom conclusions "
                          "to match original assertions instead of trusting them; "
                          "ordinary asserted leaves always require membership")
    ap.add_argument("--timeout", type=float, default=10,
                     help="solver timeout in seconds for --full-proof (default: 10)")
    ap.add_argument("--emit-json-fst", action="store_true",
                     help="also write a JSON-instance .fst file (see Z3ProofJson.fst/ "
                          "Z3PulseProofCheckerJson.fst) wrapping the JSON document, for "
                          "manually cross-validating against fstar.exe directly; not "
                          "needed for (and not used by) --fast-check")
    ap.add_argument("--json-fst-out", default=None,
                     help="path for the JSON-instance .fst file when --emit-json-fst is "
                          "given (default: <out without .fst>Json.fst)")
    args = ap.parse_args()

    if args.check_original_assertions and not args.full_proof:
        ap.error("--check-original-assertions requires --full-proof")
    if args.full_proof:
        if args.timeout <= 0:
            ap.error("--timeout must be positive")
        if args.emit_json_fst:
            ap.error("--emit-json-fst is only supported for equational documents")
        ctx = z3.Context(proof=True)
        solver = z3.Solver(ctx=ctx)
        solver.set(timeout=max(1, int(args.timeout * 1000)))
        if args.smt2_file is not None:
            solver.add(z3.parse_smt2_file(args.smt2_file, ctx=ctx))
            desc = "assertions from %s" % args.smt2_file
        else:
            x = z3.Bool("x", ctx=ctx)
            solver.add(z3.Xor(z3.Not(z3.Not(x)), x))
            desc = "not(not(x)) == x (via Xor refutation)"
        result = solver.check()
        if result != z3.unsat:
            reason = solver.reason_unknown() if result == z3.unknown else str(result)
            raise SystemExit("No UNSAT proof: %s" % reason)
        pf = solver.proof()
    elif args.smt2_file is not None:
        desc, pf = build_from_file(args.smt2_file)
    else:
        desc, pf = build_example()
    print("Z3 (python front-end) produced a proof for:", desc)

    root = pf if args.full_proof else find_equational_root(pf)
    if root is None:
        print("No equational subtree found in this proof; nothing to convert.", file=sys.stderr)
        sys.exit(1)
    print("%s root: %s (kind=%d), %d arg(s)"
          % ("Full-proof" if args.full_proof else "Equational-fragment",
             root.decl().name(), root.decl().kind(), root.num_args()))

    conv = ResolutionConverter() if args.full_proof else Converter()
    root_ident = conv.proof(root)

    def supported_rewrite(name):
        return name in FULL_PROOF_REWRITES if args.full_proof else name is not None

    matched = [(s, t, name) for (s, t, name) in conv.rewrite_log if supported_rewrite(name)]
    unmatched = [(s, t) for (s, t, name) in conv.rewrite_log if not supported_rewrite(name)]
    rewrite_obligations = sum(name not in FULL_PROOF_REWRITES
                              for _, _, name in conv.rewrite_log)
    print("Rewrite leaves: %d total, %d matched a verified lemma, %d unmatched"
          % (len(conv.rewrite_log), len(matched), len(unmatched)))

    log_path = args.log or (args.out + ".unmatched.log")
    with open(log_path, "w", encoding="utf-8") as f:
        f.write("Rewrite-rule matching log for %s\n" % desc)
        f.write("Total Rewrite leaves examined: %d\n" % len(conv.rewrite_log))
        f.write(("Matched a verified full-proof rule (diagnostic mirror): %d\n"
                 if args.full_proof else
                 "Matched a verified lemma (trusted via Z3PatternMatchedProofChecker.fst): %d\n")
                % len(matched))
        f.write("Unmatched (not verified by any known rewrite-rule lemma): %d\n\n"
                % len(unmatched))
        if args.full_proof:
            f.write("Full-proof checking discharges identity, Boolean flattening, equality "
                    "reflexivity, Boolean normalization and bounded Boolean equivalence; "
                    "other Python matcher classifications are diagnostic.\n"
                    "Pending rewrite obligations: %d\n\n" % rewrite_obligations)
        if matched:
            f.write("-- Matched leaves --\n")
            for s, t, name in matched:
                f.write("  [%s] %s  ==  %s\n" % (name, s.sexpr(), t.sexpr()))
            f.write("\n")
        if unmatched:
            f.write("-- UNVERIFIED leaves (no matching lemma found) --\n")
            for s, t in unmatched:
                if t is None:
                    f.write("  %s   (non-equational derivation step, bridged via true_marker)\n"
                            % s.sexpr())
                else:
                    f.write("  %s  ==  %s\n" % (s.sexpr(), t.sexpr()))
        else:
            f.write("(none -- every Rewrite leaf in this proof matched a verified lemma)\n")
        if args.full_proof:
            f.write("\n-- Checked theory lemmas (diagnostic mirror) --\n")
            for rule, conclusion, schema in conv.checked_theory_log:
                f.write("  [%s/%s] %s\n" % (rule, schema, conclusion.sexpr()))
            f.write("\n-- Other unverified proof-rule obligations --\n")
            for rule, conclusion in conv.trusted_log:
                f.write("  [%s] %s\n" % (rule, conclusion.sexpr()))
    print("Wrote matching log to", log_path)

    doc = (build_resolution_doc(conv, root_ident, solver.assertions(),
                               args.check_original_assertions)
           if args.full_proof else build_proof_doc(conv, root_ident, len(unmatched)))
    if args.full_proof:
        print("Def-axiom policy: %s"
              % ("exact original-assertion membership" if args.check_original_assertions
                 else "trusted leaves (ACCEPT is relative to this trust policy)"))
        print("Full-DAG rule obligations: %d; rewrite obligations: %d "
              "(verified structural rules and bounded Boolean equivalence)"
              % (len(conv.trusted_log), rewrite_obligations))
        print("Array theory lemmas matched by verified rules (diagnostic mirror): %d"
              % len(conv.checked_theory_log))
    json_out = args.json_out or (args.out + ".json")
    with open(json_out, "w", encoding="utf-8") as f:
        json_mod.dump(doc, f, separators=(",", ":"))
    print("Wrote", json_out, "(%d sort(s), %d decl(s), %d expr(s), %d proof(s))"
          % (len(doc["sorts"]), len(doc["decls"]), len(doc["exprs"]), len(doc["proofs"])))

    if args.emit_json_fst:
        json_fst_out = args.json_fst_out or (
            os.path.splitext(args.out)[0] + "Json.fst"
        )
        json_module_name = os.path.splitext(os.path.basename(json_fst_out))[0]
        json_text = generate_json_instance(json_module_name, desc, doc)
        with open(json_fst_out, "w", encoding="utf-8") as f:
            f.write(json_text)
        print("Wrote", json_fst_out, "(JSON-instance file, %d bytes of embedded JSON, "
              "for manual fstar.exe cross-validation only -- not used by --fast-check)"
              % len(json_mod.dumps(doc, separators=(",", ":"))))

    if args.fast_check:
        print("Invoking the precompiled native checker (no fstar.exe, no SMT) on", json_out, "...")
        status = run_fast_check(args.checker_exe, json_out)
        if status == "accept":
            print("PASS: the precompiled checker accepted the extracted Z3 proof (%s)." % json_out)
        elif status == "partial":
            print("PARTIAL: the full derivation checked, but unverified leaf "
                  "obligations remain; this is not an independently certified "
                  "UNSAT proof.", file=sys.stderr)
            sys.exit(3)
        else:
            print("FAIL: the precompiled checker rejected %s." % json_out, file=sys.stderr)
            sys.exit(1)


if __name__ == "__main__":
    main()
