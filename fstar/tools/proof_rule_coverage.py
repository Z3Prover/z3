"""
proof_rule_coverage.py

Walks the *entire* raw Z3 proof DAG for sampled QF_AX/QF_UF benchmarks
(same traversal as proof_rule_histogram.py) and classifies every
proof-rule-name occurrence into:

  Tier 1     - mechanically verified in Z3ProofTheory.fst (equational
               calculus: Refl/Sym/Trans/Congr) or
               Z3ResolutionProofTheory.fst (resolution/propositional
               layer: unit-resolution, and-elim, not-or-elim, mp,
               commutativity, iff-true/iff-false, array-ext,
               hypothesis, lemma -- the last two since "Round 2": see
               `Hyp`/`RLemma` + `hyps_closed`/`hyps_closed_units` in
               Z3ResolutionProofTheory.fst, confirmed already fully
               implemented and verified per
               RESOLUTION_CHECKER_SCOPE.md's "Round 2 candidates
               (status: done)" section).
  Tier 2     - modeled as an explicit `Trusted` leaf, matching the
               exact boundary Z3's own src/ast/proofs/proof_checker.cpp
               itself trusts without full verification (th-lemma for
               non-arith theories, def-axiom, quant-inst, hyper-res,
               asserted input leaves -- "asserted" stays Tier 2 because
               it is the user's own top-level input assumption, not a
               derived step with a soundness obligation to recheck).
  Unmodeled  - rule names this project's F* checker has no
               representation for at all yet.

Usage: python proof_rule_coverage.py <benchmark_dir> <n_files>
"""
import sys, os, collections, random
sys.path.insert(0, r"C:\z3fstar\fstar\tools")
import z3

# `SortKind.Z3_PROOF_SORT == 1000`: used to discriminate real proof
# nodes from their embedded conclusion-formula arguments.
Z3_PROOF_SORT_KIND = 1000

TIER1 = {
    "reflexivity", "symm", "trans", "monotonicity",
    "unit-resolution", "and-elim", "not-or-elim", "mp", "mp~",
    "commutativity", "iff-true", "iff-false", "array-ext",
    # Round 2 (`Hyp`/`RLemma` constructors + `hyps_closed`/
    # `hyps_closed_units` bookkeeping in Z3ResolutionProofTheory.fst):
    # `PR_HYPOTHESIS` only discharges when the assumed formula is
    # actually a member of the ambient hypothesis list threaded
    # through `lemma_rproof_sound_hyps`, and `PR_LEMMA` is a genuine
    # classical proof-by-contradiction (`pf_false` must close `False`
    # under exactly the single local hypothesis `(not fact_)`) -- both
    # are mechanically checked, not silently trusted.
    "hypothesis", "lemma",
}
# `trans*` bundles an un-reconstructed cycle/XOR-vertex argument
# (proof_checker.cpp's own PR_TRANSITIVITY_STAR handling) -- not yet
# mechanized, so it stays out of TIER1 even though plain `trans` is.
TIER2 = {
    "th-lemma", "def-axiom", "quant-inst",
    "hyper-res", "asserted", "trans*", "rewrite", "rewrite*",
    "quant-intro", "distributivity", "nnf-pos", "nnf-neg", "skolemize",
    "pull-quant", "push-quant", "elim-unused", "der", "apply-def",
    "iff~", "quant-inst*",
}

def rule_name(p):
    return p.decl().name()

def walk(pf, seen, hist):
    stack = [pf]
    while stack:
        node = stack.pop()
        if node.sort().kind() != Z3_PROOF_SORT_KIND:
            # Proof-rule applications carry their conclusion formula as
            # a trailing argument (e.g. `(mp p1 p2 Q)` where `Q` is an
            # ordinary Bool expr, not a sub-proof) -- `children()` walks
            # it just like any other AST child. Skip non-proof nodes
            # entirely so formula decls ("=", "not", "select", free
            # variable names, ...) never get misclassified as rules.
            continue
        key = node.get_id() if hasattr(node, "get_id") else id(node)
        if key in seen:
            continue
        seen.add(key)
        try:
            name = rule_name(node)
        except Exception:
            name = "?"
        hist[name] += 1
        try:
            kids = node.children()
        except Exception:
            kids = []
        stack.extend(kids)

def classify(name):
    if name in TIER1:
        return "tier1"
    if name in TIER2:
        return "tier2"
    return "unmodeled"

def analyze_dir(root, n):
    files = []
    for dirpath, _, filenames in os.walk(root):
        for fn in filenames:
            if fn.endswith(".smt2"):
                files.append(os.path.join(dirpath, fn))
    random.seed(42)
    random.shuffle(files)
    files = files[:n]

    node_totals = collections.Counter()   # tier -> total proof-node count
    rule_totals = collections.Counter()   # rule name -> count (for unmodeled detail)
    files_fully_covered = 0
    files_ok = 0
    unmodeled_rule_files = collections.Counter()

    for p in files:
        z3.set_param("proof", True)
        ctx = z3.Context()
        s = z3.Solver(ctx=ctx)
        s.set("timeout", 10000)
        try:
            s.add(z3.parse_smt2_file(p, ctx=ctx))
        except Exception:
            continue
        r = s.check()
        if str(r) != "unsat":
            continue
        try:
            pf = s.proof()
        except Exception:
            continue
        files_ok += 1
        hist = collections.Counter()
        walk(pf, set(), hist)
        file_unmodeled = False
        for name, cnt in hist.items():
            tier = classify(name)
            node_totals[tier] += cnt
            rule_totals[name] += cnt
            if tier == "unmodeled":
                file_unmodeled = True
                unmodeled_rule_files[name] += 1
        if not file_unmodeled:
            files_fully_covered += 1

    total_nodes = sum(node_totals.values())
    print("=== %s (sampled %d files, %d produced unsat proofs) ===" % (root, len(files), files_ok))
    print()
    print("Proof-node coverage (deduplicated by node id, aggregated over all files):")
    for tier in ("tier1", "tier2", "unmodeled"):
        cnt = node_totals[tier]
        pct = 100.0 * cnt / total_nodes if total_nodes else 0.0
        print("  %-10s %10d nodes  (%5.1f%%)" % (tier, cnt, pct))
    print()
    print("File-level coverage (entire proof within Tier1 u Tier2, nothing unmodeled):")
    pct_files = 100.0 * files_fully_covered / files_ok if files_ok else 0.0
    print("  %d / %d files (%.1f%%)" % (files_fully_covered, files_ok, pct_files))
    print()
    if unmodeled_rule_files:
        print("Unmodeled rule names observed (rule -> #files containing it):")
        for name, cnt in unmodeled_rule_files.most_common(20):
            print("  %-25s in %d/%d files, %d total nodes" % (name, cnt, files_ok, rule_totals[name]))
    print()
    return node_totals, files_fully_covered, files_ok

if __name__ == "__main__":
    analyze_dir(sys.argv[1], int(sys.argv[2]))
