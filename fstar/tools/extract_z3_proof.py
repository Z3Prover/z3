#!/usr/bin/env python3
"""
extract_z3_proof.py

Uses Z3's *Python* front-end (the `z3` module, i.e. z3py) to produce a
real proof object for a small example, pretty-prints the equational
fragment of that proof object into the literal F* syntax
`Z3ProofTheory.fst`'s `proof`/`Z3AstTheory.fst`'s `expr` datatypes
accept, and invokes the Pulse-verified checker (`Z3PulseProofChecker
.fst`'s `checker_accepts`/`check_proof`) on the result by shelling out
to `fstar.exe` (there is no other way to "run" a Pulse program; F*
type-checking *is* running it).

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
    python extract_z3_proof.py [smt2-file] [--check] [--out FILE.fst]

If `smt2-file` is omitted, a small built-in example is used instead
(`not(not(x)) == x`, refuted by negation). If given, its assertions
are parsed and checked; they must be jointly unsatisfiable (there is
no refutation proof to extract from a `sat` result).

With `--check`, additionally shells out to `fstar.exe` (path below,
same toolchain invocation used throughout `fstar/`) to actually run
the Pulse checker on the generated file and reports the verdict.
"""
import argparse
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


def fstar_ident(prefix, n):
    return "%s%d" % (prefix, n)


class Converter:
    def __init__(self):
        self.sort_lines = []
        self.decl_lines = []
        self.expr_lines = []
        self.proof_lines = []
        self.sort_cache = {}   # sort name -> ident
        self.decl_cache = {}   # (name, arity) -> ident
        self.expr_cache = {}   # z3 ast id -> ident
        self.proof_cache = {}  # z3 ast id -> ident
        self.true_marker_emitted = False

    # ---- sorts -----------------------------------------------------
    def sort(self, s: z3.SortRef) -> str:
        name = s.name()
        if name in self.sort_cache:
            return self.sort_cache[name]
        ident = fstar_ident("srt_", len(self.sort_cache))
        if s.kind() == z3.Z3_ARRAY_SORT:
            # Multi-argument arrays expose domain_n()/domain(i); plain
            # single-index arrays only expose domain(). Prefer the
            # former when available so Z3's own multi-dimensional
            # arrays round-trip into `ArraySort`'s `list sort` domain.
            if hasattr(s, "domain_n"):
                dom = [self.sort(s.domain_n(i)) for i in range(s.arity())]
            else:
                dom = [self.sort(s.domain())]
            rng = self.sort(s.range())
            self.sort_lines.append(
                "let %s : sort = ArraySort [%s] %s" % (ident, "; ".join(dom), rng)
            )
        else:
            self.sort_lines.append('let %s : sort = BaseSort "%s"' % (ident, name))
        self.sort_cache[name] = ident
        return ident

    # ---- func_decls (always emitted as uninterpreted: `fact`/        -
    # `check_proof` never consult `interp`/`domain`, only `decl_name`  -
    # +structural shape, so this is a faithful, lossless-for-our-      -
    # purposes simplification) ---------------------------------------
    def func_decl(self, d: z3.FuncDeclRef, arity: int) -> str:
        key = (d.name(), arity)
        if key in self.decl_cache:
            return self.decl_cache[key]
        ident = fstar_ident("fd_", len(self.decl_cache))
        dom = [self.sort(d.domain(i)) for i in range(arity)]
        rng = self.sort(d.range())
        self.decl_lines.append(
            'let %s : func_decl = { decl_name = "%s"; domain = [%s]; range = %s; '
            'interp = None; int_params = [] }'
            % (ident, d.name(), "; ".join(dom), rng)
        )
        self.decl_cache[key] = ident
        return ident

    def true_marker(self) -> str:
        if not self.true_marker_emitted:
            bool_s = self.sort(z3.BoolSort())
            self.decl_lines.append(
                'let fd_true_marker : func_decl = '
                '{ decl_name = "true_marker"; domain = []; range = %s; '
                'interp = None; int_params = [] }' % bool_s
            )
            self.true_marker_emitted = True
        return "fd_true_marker"

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
                body_sort = self.sort(e.body().sort())
                qsort = "(ArraySort [%s] %s)" % ("; ".join(bound_sorts), body_sort)
            else:
                qk = "Forall_k" if e.is_forall() else "Exists_k"
                qsort = '(BaseSort "Bool")'
            ident = fstar_ident("e_", len(self.expr_cache))
            self.expr_lines.append(
                "let %s : expr = Quantifier %s [%s] %s %s"
                % (ident, qk, "; ".join(bound_sorts), qsort, body)
            )
        elif z3.is_var(e):
            idx = z3.get_var_index(e)
            s = self.sort(e.sort())
            ident = fstar_ident("e_", len(self.expr_cache))
            self.expr_lines.append("let %s : expr = Var %d %s" % (ident, idx, s))
        else:
            args = [self.expr(e.arg(i)) for i in range(e.num_args())]
            d = self.func_decl(e.decl(), e.num_args())
            ident = fstar_ident("e_", len(self.expr_cache))
            self.expr_lines.append(
                "let %s : expr = App %s [%s]" % (ident, d, "; ".join(args))
            )
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
            s = self.expr(concl.arg(0))
            t = self.expr(concl.arg(1))
        else:
            s = self.expr(concl)
            fd = self.true_marker()
            t_ident = fstar_ident("e_", len(self.expr_cache))
            self.expr_lines.append("let %s : expr = App %s []" % (t_ident, fd))
            t = t_ident
        ident = fstar_ident("p_", len(self.proof_cache))
        self.proof_lines.append("let %s : proof = Rewrite %s %s" % (ident, s, t))
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
        elif kind == z3.Z3_OP_PR_SYMMETRY:
            p1 = self.proof(premises[0], depth + 1, max_depth)
            ident = fstar_ident("p_", len(self.proof_cache))
            self.proof_lines.append("let %s : proof = Sym %s" % (ident, p1))
        elif kind in (z3.Z3_OP_PR_TRANSITIVITY, z3.Z3_OP_PR_TRANSITIVITY_STAR) and len(premises) == 2:
            p1 = self.proof(premises[0], depth + 1, max_depth)
            p2 = self.proof(premises[1], depth + 1, max_depth)
            ident = fstar_ident("p_", len(self.proof_cache))
            self.proof_lines.append("let %s : proof = Trans %s %s" % (ident, p1, p2))
        elif kind == z3.Z3_OP_PR_MONOTONICITY:
            lhs, rhs = concl.arg(0), concl.arg(1)
            f = self.func_decl(lhs.decl(), lhs.num_args())
            args1 = "; ".join(self.expr(lhs.arg(i)) for i in range(lhs.num_args()))
            args2 = "; ".join(self.expr(rhs.arg(i)) for i in range(rhs.num_args()))
            prfs = [self.proof(pr, depth + 1, max_depth) for pr in premises]
            ident = fstar_ident("p_", len(self.proof_cache))
            self.proof_lines.append(
                "let %s : proof = Congr %s [%s] [%s] [%s]"
                % (ident, f, args1, args2, "; ".join(prfs))
            )
        elif kind in (z3.Z3_OP_PR_REWRITE, z3.Z3_OP_PR_REWRITE_STAR):
            s = self.expr(concl.arg(0))
            t = self.expr(concl.arg(1))
            ident = fstar_ident("p_", len(self.proof_cache))
            self.proof_lines.append("let %s : proof = Rewrite %s %s" % (ident, s, t))
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
open Z3ProofTheory
open Z3PulseProofChecker

"""


def generate(module_name, example_desc, conv: Converter, root_ident: str) -> str:
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("smt2_file", nargs="?", default=None,
                     help="path to an .smt2 file whose assertions are jointly "
                          "unsatisfiable; if omitted, uses the built-in "
                          "not(not(x)) == x example")
    ap.add_argument("--out", default="Z3ExtractedProof.fst")
    ap.add_argument("--check", action="store_true",
                     help="shell out to fstar.exe and run the Pulse checker on the result")
    ap.add_argument("--fstar", default=r"C:\fstar\fstar\bin\fstar.exe")
    ap.add_argument("--z3-smt", default=r"C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe")
    args = ap.parse_args()

    if args.smt2_file is not None:
        desc, pf = build_from_file(args.smt2_file)
    else:
        desc, pf = build_example()
    print("Z3 (python front-end) produced a proof for:", desc)

    root = find_equational_root(pf)
    if root is None:
        print("No equational subtree found in this proof; nothing to convert.", file=sys.stderr)
        sys.exit(1)
    print("Equational-fragment root found: %s (kind=%d), %d arg(s)"
          % (root.decl().name(), root.decl().kind(), root.num_args()))

    conv = Converter()
    root_ident = conv.proof(root)
    module_name = os.path.splitext(os.path.basename(args.out))[0]
    text = generate(module_name, desc, conv, root_ident)
    with open(args.out, "w") as f:
        f.write(text)
    print("Wrote", args.out, "(%d proof node(s), %d expr node(s))"
          % (len(conv.proof_lines), len(conv.expr_lines)))

    if args.check:
        print("Invoking the Pulse-verified checker via fstar.exe ...")
        cmd = [args.fstar, "--smt", args.z3_smt, args.out]
        res = subprocess.run(cmd, cwd=".", capture_output=True, text=True)
        print(res.stdout[-4000:])
        print(res.stderr[-2000:])
        if res.returncode == 0 and "All verification conditions discharged successfully" in res.stdout:
            print("PASS: the Pulse proof checker accepted the extracted Z3 proof.")
        else:
            print("FAIL: fstar.exe did not fully verify the generated file.", file=sys.stderr)
            sys.exit(1)


if __name__ == "__main__":
    main()
