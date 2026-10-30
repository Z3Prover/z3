# F* audit of PR #11436 @ 38fdd8db1ea3ba3394908ef20b9a654113d29b59 (base c95b61cb)
Scope (partial): `literals`/`literal_arguments`, `same_literals`, `equality_reduction` in fstar/Z3Tptp.fst (sha256 70b5c06b...). Source read via contents API at head SHA.
Obligations (all proved in Z3TptpLiteralAudit.fst):
1. literals flattening: clause semantics of lits(p,f) equals f (p) / not f (not p), for well-formed fragments (Or positive, And negative, Imp positive), with false/true literals dropped.
2. same_literals mutual containment preserves clause truth value.
3. equality_reduction dropping negative reflexive-equality literals preserves clause truth, assuming reflexive atoms are valid.
Correspondence: abstract fm/lit model over int atoms; polarity handling mirrors the C++-free F* source. Atoms of other shape (e.g. Or under negative polarity) are treated as opaque literals; same_atom's symmetric-equation rule is not modelled (atom equality abstracted to structural equality), nor Horn check, quantifier handling (Z3QuantifierReduce.equivalent), or sort handling.
Excluded: Z3DirectProof.fst, Z3Cherry.fst, rendering/symbol naming, visit/quantified_instance, Python/OCaml/C++ tooling and tests, docs, example files, prior audit dirs.
Assumptions: F* standard library; model is a semantic model, not verification of extracted code. Reflexive-equality validity assumed for obligation 3.
No counterexample sought beyond review; none found. Versions: F* 2026.09.27, Z3 4.13.3.
Reproduce: fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Z3TptpLiteralAudit.fst