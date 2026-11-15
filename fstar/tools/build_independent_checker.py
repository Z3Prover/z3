"""Extract and link the prototype checker without legacy value semantics."""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

import checker_scope


ROOT = Path(__file__).resolve().parents[1]
RUNTIME = [
    "prims.ml", "Custard_Prims.ml", "fStar_Pervasives.ml",
    "fStar_Pervasives_Native.ml", "fStar_List_Tot_Base.ml", "fStar_String.ml",
    "fStar_UInt.ml", "fStar_FunctionalExtensionality.ml", "Z3Native.ml",
    "Z3IndependentMain.ml",
]
SCOPED_VARIABLE_LOOKUP = (
    "((Prims.op_Less n (FStar_List_Tot_Base.length scope)) && "
    "((=) (FStar_List_Tot_Base.index scope n) s))")


def run(command, *, cwd, timeout, env=None):
    print("+", " ".join(map(str, command)), flush=True)
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True, timeout=timeout,
                            env=env)
    if result.returncode:
        print(result.stdout, end="")
        print(result.stderr, end="")
        result.check_returncode()
    return result


def scope_lookup_body(text):
    bindings = re.findall(r"(?ms)^let matches\b[^\n]*=\n(.*?)(?=\n(?:let |type )|\Z)", text)
    if (len(bindings) != 1 or text.count("if ((=) n Prims.int_zero)") != 1 or
            text.count(SCOPED_VARIABLE_LOOKUP) != 1):
        raise RuntimeError("Unexpected extracted scope lookup fallback")
    return bindings[0].strip()


def realize_scope_lookup(text, scope_source=None):
    if text.count(SCOPED_VARIABLE_LOOKUP) != 1:
        raise RuntimeError("Unexpected extracted scoped variable lookup")
    return text.replace(SCOPED_VARIABLE_LOOKUP, scope_lookup_body(scope_source or ""))


def prepare_extracted_source(name, text, *, contextual_source=None, scope_source=None):
    lines = text.splitlines()
    lines.insert(2, "open Prims")
    rendered = ("\n".join(lines) + "\n").replace(
        "(fun s -> BatList.init (BatUTF8.length s) (fun i -> BatUChar.code (BatUTF8.get s i)))",
        "FStar_String.list_of_string")
    if name == "Z3BinderScopeSyntax.ml":
        original = (
            "let name_length (s : string) : Prims.int =\n"
            "  (count_cells Prims.int_zero (FStar_String.list_of_string s))")
        if rendered.count(original) != 1:
            raise RuntimeError("Unexpected extracted binder name_length binding")
        # Z3BinderScopeIndependent.lemma_name_length proves this identity.
        rendered = rendered.replace(original, (
            "let name_length (s : string) : Prims.int =\n"
            "  (FStar_String.strlen s)"))
    if name == "Z3BooleanNormalForm.ml":
        binding = r"(?ms)^let contextual_equivalent\b.*?(?=\n(?:let |type )|\Z)"
        replacements = re.findall(binding, contextual_source or "")
        if len(replacements) != 1 or len(re.findall(binding, rendered)) != 1:
            raise RuntimeError("Missing or duplicate verified contextual_equivalent binding")
        # Inline the verified equivalent body, avoiding a native module cycle.
        replacement = replacements[0].replace("Z3BooleanNormalForm.", "")
        rendered = re.sub(binding, lambda _: replacement, rendered)
    if name == "Z3ExprScope.ml":
        rendered = realize_scope_lookup(rendered, scope_source)
    if name == "Z3IndependentScopeLookup.ml":
        # Preserve the original fallback even outside the verified nat domain.
        scope_lookup_body(rendered)
    if re.search(r"Bat[A-Z][A-Za-z0-9_]*\.", rendered):
        raise RuntimeError(f"Unsupported Batteries dependency in {name}")
    return rendered


def build(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    extract = output / "extract"
    extract.mkdir()
    manifest = json.loads((ROOT / "tools" / "checker_modules.json").read_text())
    closure = checker_scope.dependency_closure(
        checker_scope.dependency_command(
            args.fstar, ["Z3IndependentNative.fst"]))
    if "Z3ValueTheory.fst" in closure or "Z3UnifiedProof.fst" in closure:
        raise RuntimeError("Independent checker imports legacy value semantics")
    registered = manifest["modules"] + manifest["tests"]
    missing = closure - set(registered + manifest["cherry_modules"])
    if missing:
        raise RuntimeError(f"Unregistered dependencies: {sorted(missing)}")
    command = [
        str(args.fstar), "--warn_error", "@1..999", "--cache_dir", str(args.cache_dir),
        "--include", str(args.cache_dir), "--smt", str(args.z3_exe),
        "--z3version", args.z3_version, "--codegen", "OCaml", "--custard_split",
        "--odir", str(extract),
    ]
    for module in ("Z3IndependentNative", "Z3NativeProof", "Z3IndependentChecker",
                   "Z3IndependentFiniteFieldWitness", "Z3IndependentFiniteFieldReplay",
                   "Z3IndependentFiniteFieldDocument",
                   "Z3IndependentArrayDocument", "Z3IndependentGroundDefinition",
                   "Z3IndependentDefinitionDocument", "Z3IndependentDefinitionNnfDocument",
                   "Z3IndependentDefinitionSkolemReplay", "Z3IndependentDefinitionSkolemDocument",
                   "Z3IndependentBooleanContext", "Z3IndependentCertificateFallback",
                   "Z3IndependentRootReplay", "Z3IndependentScopeLookup",
                   "Z3IndependentCachedReplay"):
        command.extend(["--custard_entry_module", module])
    command.append("Z3IndependentNative.fst")
    run(command, cwd=ROOT, timeout=args.timeout)

    for name in RUNTIME:
        shutil.copyfile(ROOT / "ocaml_runtime" / name, output / name)
    contextual_source = (extract / "Z3IndependentBooleanContext.ml").read_text(encoding="utf-8")
    scope_source = (extract / "Z3IndependentScopeLookup.ml").read_text(encoding="utf-8")
    for source in extract.glob("*.ml"):
        if source.name in RUNTIME or source.name == "Z3IndependentBooleanContext.ml":
            continue
        rendered = prepare_extracted_source(
            source.name, source.read_text(encoding="utf-8"),
            contextual_source=contextual_source, scope_source=scope_source)
        (output / source.name).write_text(rendered, encoding="utf-8")
    files = sorted(path.name for path in output.glob("*.ml"))
    if "Z3ValueTheory.ml" in files:
        raise RuntimeError("Legacy value theory was extracted")
    include = args.install_dir / "lib" / "ocaml" / "z3"
    order = run(["ocamlfind", "ocamldep", "-I", str(include), "-sort", *files],
                cwd=output, timeout=args.timeout).stdout.split()
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "-I", str(include), "-ccopt", f"-L{args.install_dir / 'lib'}",
         "z3ml.cmxa", *order, "-o", "checker"], cwd=output, timeout=args.timeout)
    test = "test_independent_skolem_replay.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    objects = [str(Path(name).with_suffix(".cmx")) for name in order
               if name not in ("Z3IndependentMain.ml", "Z3IndependentNative.ml")]
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "-I", str(include), "-ccopt", f"-L{args.install_dir / 'lib'}",
         "z3ml.cmxa", *objects, test, "-o", "test_independent_skolem_replay"],
        cwd=output, timeout=args.timeout)
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = os.pathsep.join(
        filter(None, [str(args.install_dir / "lib"), env.get("LD_LIBRARY_PATH")]))
    run([str(output / "test_independent_skolem_replay")], cwd=output,
        timeout=args.timeout, env=env)
    test = "test_independent_dependent_replay.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "-I", str(include), "-ccopt", f"-L{args.install_dir / 'lib'}",
         "z3ml.cmxa", *objects, test, "-o", "test_independent_dependent_replay"],
        cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_dependent_replay")], cwd=output,
        timeout=args.timeout, env=env)
    test = "test_independent_cached_replay.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "-I", str(include), "-ccopt", f"-L{args.install_dir / 'lib'}",
         "z3ml.cmxa", *objects, test, "-o", "test_independent_cached_replay"],
        cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_cached_replay")], cwd=output,
        timeout=args.timeout, env=env)
    test = "test_independent_binder_replay.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "-I", str(include), "-ccopt", f"-L{args.install_dir / 'lib'}",
         "z3ml.cmxa", *objects, test, "-o", "test_independent_binder_replay"],
        cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_binder_replay")], cwd=output,
        timeout=args.timeout, env=env)
    test = "test_independent_boolean_context.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "-I", str(include), "-ccopt", f"-L{args.install_dir / 'lib'}",
         "z3ml.cmxa", *objects, test, "-o", "test_independent_boolean_context"],
        cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_boolean_context")], cwd=output,
        timeout=args.timeout, env=env)
    test = "test_independent_scope_lookup.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "-I", str(include), "-ccopt", f"-L{args.install_dir / 'lib'}",
         "z3ml.cmxa", *objects, test, "-o", "test_independent_scope_lookup"],
        cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_scope_lookup")], cwd=output,
        timeout=args.timeout, env=env)
    test = "test_independent_finite_field_document.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "-I", str(include), "-ccopt", f"-L{args.install_dir / 'lib'}",
         "z3ml.cmxa", *objects, test, "-o", "test_independent_finite_field_document"],
        cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_finite_field_document")], cwd=output,
        timeout=args.timeout, env=env)
    prime_extract = output / "prime-extract"
    prime_extract.mkdir()
    run([
        str(args.fstar), "--warn_error", "@1..999", "--cache_dir", str(args.cache_dir),
        "--include", str(args.cache_dir), "--smt", str(args.z3_exe),
        "--z3version", args.z3_version, "--codegen", "OCaml", "--custard_split",
        "--odir", str(prime_extract), "--custard_entry_module", "Z3IndependentFiniteFieldPrime",
        "Z3IndependentFiniteFieldPrime.fst",
    ], cwd=ROOT, timeout=args.timeout)
    prime_source = (prime_extract / "Z3IndependentFiniteFieldPrime.ml").read_text(
        encoding="utf-8").splitlines()
    prime_source.insert(2, "open Prims")
    (output / "Z3IndependentFiniteFieldPrime.ml").write_text(
        "\n".join(prime_source) + "\n", encoding="utf-8")
    test = "test_independent_finite_field_prime.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "prims.cmx", "Z3IndependentFiniteFieldPrime.ml", test,
         "-o", "test_independent_finite_field_prime"], cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_finite_field_prime")], cwd=output,
        timeout=args.timeout, env=env)
    modpow_extract = output / "modpow-extract"
    modpow_extract.mkdir()
    run([
        str(args.fstar), "--warn_error", "@1..999", "--cache_dir", str(args.cache_dir),
        "--include", str(args.cache_dir), "--smt", str(args.z3_exe),
        "--z3version", args.z3_version, "--codegen", "OCaml", "--custard_split",
        "--odir", str(modpow_extract), "--custard_entry_module", "Z3IndependentModPow",
        "Z3IndependentModPow.fst",
    ], cwd=ROOT, timeout=args.timeout)
    modpow_source = (modpow_extract / "Z3IndependentModPow.ml").read_text(
        encoding="utf-8").splitlines()
    modpow_source.insert(2, "open Prims")
    (output / "Z3IndependentModPow.ml").write_text(
        "\n".join(modpow_source) + "\n", encoding="utf-8")
    test = "test_independent_mod_pow.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "prims.cmx", "Z3IndependentModPow.ml", test,
         "-o", "test_independent_mod_pow"], cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_mod_pow")], cwd=output,
        timeout=args.timeout, env=env)
    coprime_extract = output / "coprime-extract"
    coprime_extract.mkdir()
    run([
        str(args.fstar), "--warn_error", "@1..999", "--cache_dir", str(args.cache_dir),
        "--include", str(args.cache_dir), "--smt", str(args.z3_exe),
        "--z3version", args.z3_version, "--codegen", "OCaml", "--custard_split",
        "--odir", str(coprime_extract), "--custard_entry_module", "Z3IndependentCoprimePower",
        "Z3IndependentCoprimePower.fst",
    ], cwd=ROOT, timeout=args.timeout)
    coprime_sources = ["FStar_Math_Euclid.ml", "Z3IndependentModPow.ml",
                       "Z3IndependentCoprimePower.ml"]
    for name in coprime_sources:
        source = (coprime_extract / name).read_text(encoding="utf-8").splitlines()
        source.insert(2, "open Prims")
        (output / name).write_text("\n".join(source) + "\n", encoding="utf-8")
    test = "test_independent_coprime_power.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "prims.cmx", *coprime_sources, test,
         "-o", "test_independent_coprime_power"], cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_coprime_power")], cwd=output,
        timeout=args.timeout, env=env)
    evidence_extract = output / "prime-evidence-extract"
    evidence_extract.mkdir()
    run([
        str(args.fstar), "--warn_error", "@1..999", "--cache_dir", str(args.cache_dir),
        "--include", str(args.cache_dir), "--smt", str(args.z3_exe),
        "--z3version", args.z3_version, "--codegen", "OCaml", "--custard_split",
        "--odir", str(evidence_extract), "--custard_entry_module", "Z3IndependentPrimeEvidence",
        "Z3IndependentPrimeEvidence.fst",
    ], cwd=ROOT, timeout=args.timeout)
    evidence_sources = ["FStar_Math_Euclid.ml", "Z3IndependentModPow.ml",
                        "Z3IndependentFiniteFieldPrime.ml", "Z3IndependentFactorPrime.ml",
                        "Z3IndependentCoprimePower.ml",
                        "Z3IndependentPrimeEvidence.ml"]
    for name in evidence_sources:
        source = (evidence_extract / name).read_text(encoding="utf-8").splitlines()
        source.insert(2, "open Prims")
        (output / name).write_text("\n".join(source) + "\n", encoding="utf-8")
    test = "test_independent_prime_evidence.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "prims.cmx", *evidence_sources, test,
         "-o", "test_independent_prime_evidence"], cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_prime_evidence")], cwd=output,
        timeout=args.timeout, env=env)
    index_extract = output / "index-extract"
    index_extract.mkdir()
    run([
        str(args.fstar), "--warn_error", "@1..999", "--cache_dir", str(args.cache_dir),
        "--include", str(args.cache_dir), "--smt", str(args.z3_exe),
        "--z3version", args.z3_version, "--codegen", "OCaml", "--custard_split",
        "--odir", str(index_extract), "--custard_entry_module", "Z3ProofIndex",
        "--custard_entry_module", "Z3IndependentProofIndex", "Z3IndependentProofIndex.fst",
    ], cwd=ROOT, timeout=args.timeout)
    for name in ("Z3ProofIndex.ml", "Z3IndependentProofIndex.ml"):
        source = (index_extract / name).read_text(encoding="utf-8").splitlines()
        source.insert(2, "open Prims")
        (index_extract / name).write_text("\n".join(source) + "\n", encoding="utf-8")
    for name in ("prims.ml", "fStar_List_Tot_Base.ml"):
        shutil.copyfile(output / name, index_extract / name)
    test = "test_independent_proof_index.ml"
    shutil.copyfile(ROOT / "tools" / test, index_extract / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "prims.ml", "fStar_List_Tot_Base.ml", "Z3ProofIndex.ml",
         "Z3IndependentProofIndex.ml", test, "-o", "test_independent_proof_index"],
        cwd=index_extract, timeout=args.timeout)
    run([str(index_extract / "test_independent_proof_index")], cwd=index_extract,
        timeout=args.timeout, env=env)
    monomial_extract = output / "monomial-extract"
    monomial_extract.mkdir()
    run([
        str(args.fstar), "--warn_error", "@1..999", "--cache_dir", str(args.cache_dir),
        "--include", str(args.cache_dir), "--smt", str(args.z3_exe),
        "--z3version", args.z3_version, "--codegen", "OCaml", "--custard_split",
        "--odir", str(monomial_extract), "--custard_entry_module",
        "Z3IndependentFiniteFieldMonomial", "Z3IndependentFiniteFieldMonomial.fst",
    ], cwd=ROOT, timeout=args.timeout)
    monomial_sources = ["FStar_Math_Fermat.ml", "Z3IndependentFiniteFieldMonomial.ml"]
    for name in monomial_sources:
        source = (monomial_extract / name).read_text(encoding="utf-8").splitlines()
        source.insert(2, "open Prims")
        (output / name).write_text("\n".join(source) + "\n", encoding="utf-8")
    test = "test_independent_finite_field_monomial.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "prims.cmx", *monomial_sources, test,
         "-o", "test_independent_finite_field_monomial"], cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_finite_field_monomial")], cwd=output,
        timeout=args.timeout, env=env)
    polynomial_extract = output / "polynomial-extract"
    polynomial_extract.mkdir()
    run([
        str(args.fstar), "--warn_error", "@1..999", "--cache_dir", str(args.cache_dir),
        "--include", str(args.cache_dir), "--smt", str(args.z3_exe),
        "--z3version", args.z3_version, "--codegen", "OCaml", "--custard_split",
        "--odir", str(polynomial_extract), "--custard_entry_module",
        "Z3IndependentFiniteFieldPolynomial", "Z3IndependentFiniteFieldPolynomial.fst",
    ], cwd=ROOT, timeout=args.timeout)
    polynomial_sources = [
        "FStar_Math_Fermat.ml", "Z3IndependentFiniteFieldMonomial.ml",
        "Z3IndependentFiniteFieldPolynomial.ml",
    ]
    for name in polynomial_sources:
        source = (polynomial_extract / name).read_text(encoding="utf-8").splitlines()
        source.insert(2, "open Prims")
        (output / name).write_text("\n".join(source) + "\n", encoding="utf-8")
    test = "test_independent_finite_field_polynomial.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "prims.cmx", "fStar_List_Tot_Base.cmx", *polynomial_sources, test,
         "-o", "test_independent_finite_field_polynomial"], cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_finite_field_polynomial")], cwd=output,
        timeout=args.timeout, env=env)
    budget_extract = output / "budget-extract"
    budget_extract.mkdir()
    run([
        str(args.fstar), "--warn_error", "@1..999", "--cache_dir", str(args.cache_dir),
        "--include", str(args.cache_dir), "--smt", str(args.z3_exe),
        "--z3version", args.z3_version, "--codegen", "OCaml", "--custard_split",
        "--odir", str(budget_extract), "--custard_entry_module",
        "Z3IndependentFiniteFieldBudget", "Z3IndependentFiniteFieldBudget.fst",
    ], cwd=ROOT, timeout=args.timeout)
    budget_sources = ["FStar_Math_Fermat.ml", "Z3IndependentFiniteFieldMonomial.ml",
                      "Z3IndependentFiniteFieldPolynomial.ml",
                      "Z3IndependentFiniteFieldBudget.ml"]
    for name in budget_sources:
        directory = (budget_extract if name == "Z3IndependentFiniteFieldBudget.ml"
                     else polynomial_extract if name == "Z3IndependentFiniteFieldPolynomial.ml"
                     else monomial_extract)
        source = (directory / name).read_text(encoding="utf-8").splitlines()
        source.insert(2, "open Prims")
        (output / name).write_text("\n".join(source) + "\n", encoding="utf-8")
    test = "test_independent_finite_field_budget.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "prims.cmx", "fStar_List_Tot_Base.cmx", *budget_sources, test,
         "-o", "test_independent_finite_field_budget"], cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_finite_field_budget")], cwd=output,
        timeout=args.timeout, env=env)
    replay_extract = output / "compact-replay-extract"
    replay_extract.mkdir()
    run([
        str(args.fstar), "--warn_error", "@1..999", "--cache_dir", str(args.cache_dir),
        "--include", str(args.cache_dir), "--smt", str(args.z3_exe),
        "--z3version", args.z3_version, "--codegen", "OCaml", "--custard_split",
        "--odir", str(replay_extract), "--custard_entry_module",
        "Z3IndependentFiniteFieldCompactReplay", "Z3IndependentFiniteFieldCompactReplay.fst",
    ], cwd=ROOT, timeout=args.timeout)
    replay_sources = ["Z3ProofIndex.ml", "Z3IndependentFiniteFieldMonomial.ml",
                      "Z3IndependentFiniteFieldPolynomial.ml",
                      "Z3IndependentFiniteFieldCompactReplay.ml"]
    for name in replay_sources:
        source = (replay_extract / name).read_text(encoding="utf-8").splitlines()
        source.insert(2, "open Prims")
        (replay_extract / name).write_text("\n".join(source) + "\n", encoding="utf-8")
    for name in ("prims.ml", "fStar_List_Tot_Base.ml"):
        shutil.copyfile(ROOT / "ocaml_runtime" / name, replay_extract / name)
    test = "test_independent_finite_field_compact_replay.ml"
    shutil.copyfile(ROOT / "tools" / test, replay_extract / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "prims.ml", "fStar_List_Tot_Base.ml", *replay_sources, test,
         "-o", "test_compact_replay"], cwd=replay_extract, timeout=args.timeout)
    run([str(replay_extract / "test_compact_replay")], cwd=replay_extract,
        timeout=args.timeout, env=env)
    metered_extract = output / "compact-metered-extract"
    metered_extract.mkdir()
    run([
        str(args.fstar), "--warn_error", "@1..999", "--cache_dir", str(args.cache_dir),
        "--include", str(args.cache_dir), "--smt", str(args.z3_exe),
        "--z3version", args.z3_version, "--codegen", "OCaml", "--custard_split",
        "--odir", str(metered_extract), "--custard_entry_module",
        "Z3IndependentFiniteFieldCompactReplay", "--custard_entry_module",
        "Z3IndependentProofIndex", "--custard_entry_module",
        "Z3IndependentFiniteFieldCompactMetered", "Z3IndependentFiniteFieldCompactMetered.fst",
    ], cwd=ROOT, timeout=args.timeout)
    metered_sources = ["Z3ProofIndex.ml", "Z3IndependentProofIndex.ml",
                       "Z3IndependentFiniteFieldMonomial.ml",
                       "Z3IndependentFiniteFieldPolynomial.ml",
                       "Z3IndependentFiniteFieldCompactReplay.ml",
                       "Z3IndependentFiniteFieldCompactMetered.ml"]
    for name in metered_sources:
        source = (metered_extract / name).read_text(encoding="utf-8").splitlines()
        source.insert(2, "open Prims")
        (metered_extract / name).write_text("\n".join(source) + "\n", encoding="utf-8")
    for name in ("prims.ml", "fStar_List_Tot_Base.ml"):
        shutil.copyfile(ROOT / "ocaml_runtime" / name, metered_extract / name)
    test = "test_independent_finite_field_compact_metered.ml"
    shutil.copyfile(ROOT / "tools" / test, metered_extract / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "prims.ml", "fStar_List_Tot_Base.ml", *metered_sources, test,
         "-o", "test_compact_metered"], cwd=metered_extract, timeout=args.timeout)
    run([str(metered_extract / "test_compact_metered")], cwd=metered_extract,
        timeout=args.timeout, env=env)
    pac_extract = output / "compact-pac-extract"
    pac_extract.mkdir()
    run([
        str(args.fstar), "--warn_error", "@1..999", "--cache_dir", str(args.cache_dir),
        "--include", str(args.cache_dir), "--smt", str(args.z3_exe),
        "--z3version", args.z3_version, "--codegen", "OCaml", "--custard_split",
        "--odir", str(pac_extract), "--custard_entry_module",
        "Z3IndependentFiniteFieldCompactReplay", "--custard_entry_module",
        "Z3IndependentFiniteFieldCompactPac", "--custard_entry_module",
        "Z3IndependentFiniteFieldCompactPacMetered", "--custard_entry_module",
        "Z3ProofIndex", "Z3IndependentFiniteFieldCompactPacMetered.fst",
    ], cwd=ROOT, timeout=args.timeout)
    for path in pac_extract.glob("*.ml"):
        source = path.read_text(encoding="utf-8").splitlines()
        source.insert(2, "open Prims")
        path.write_text("\n".join(source) + "\n", encoding="utf-8")
    for name in ("prims.ml", "fStar_List_Tot_Base.ml"):
        shutil.copyfile(ROOT / "ocaml_runtime" / name, pac_extract / name)
    sources = sorted(path.name for path in pac_extract.glob("*.ml"))
    order = run(["ocamlfind", "ocamldep", "-sort", *sources],
                cwd=pac_extract, timeout=args.timeout).stdout.split()
    test = "test_independent_finite_field_compact_pac.ml"
    shutil.copyfile(ROOT / "tools" / test, pac_extract / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", *order, test, "-o", "test_compact_pac"],
        cwd=pac_extract, timeout=args.timeout)
    run([str(pac_extract / "test_compact_pac")], cwd=pac_extract,
        timeout=args.timeout, env=env)
    test = "test_independent_finite_field_compact_pac_metered.ml"
    shutil.copyfile(ROOT / "tools" / test, pac_extract / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", *order, test, "-o", "test_compact_pac_metered"],
        cwd=pac_extract, timeout=args.timeout)
    run([str(pac_extract / "test_compact_pac_metered")], cwd=pac_extract,
        timeout=args.timeout, env=env)
    certificate_extract = output / "compact-certificate-extract"
    certificate_extract.mkdir()
    run([
        str(args.fstar), "--warn_error", "@1..999", "--cache_dir", str(args.cache_dir),
        "--include", str(args.cache_dir), "--smt", str(args.z3_exe),
        "--z3version", args.z3_version, "--codegen", "OCaml", "--custard_split",
        "--odir", str(certificate_extract), "--custard_entry_module",
        "Z3IndependentFiniteFieldCompactCertificate", "--custard_entry_module",
        "Z3IndependentFiniteFieldWitness", "Z3IndependentFiniteFieldCompactCertificate.fst",
    ], cwd=ROOT, timeout=args.timeout)
    for path in certificate_extract.glob("*.ml"):
        source = path.read_text(encoding="utf-8").splitlines()
        source.insert(2, "open Prims")
        path.write_text("\n".join(source) + "\n", encoding="utf-8")
    for name in ("prims.ml", "fStar_List_Tot_Base.ml"):
        shutil.copyfile(ROOT / "ocaml_runtime" / name, certificate_extract / name)
    sources = sorted(path.name for path in certificate_extract.glob("*.ml"))
    order = run(["ocamlfind", "ocamldep", "-sort", *sources],
                cwd=certificate_extract, timeout=args.timeout).stdout.split()
    test = "test_independent_finite_field_compact_certificate.ml"
    shutil.copyfile(ROOT / "tools" / test, certificate_extract / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", *order, test, "-o", "test_compact_certificate"],
        cwd=certificate_extract, timeout=args.timeout)
    run([str(certificate_extract / "test_compact_certificate")], cwd=certificate_extract,
        timeout=args.timeout, env=env)
    test = "test_independent_array_document.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "-I", str(include), "-ccopt", f"-L{args.install_dir / 'lib'}",
         "z3ml.cmxa", *objects, test, "-o", "test_independent_array_document"],
        cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_array_document")], cwd=output,
        timeout=args.timeout, env=env)
    test = "test_independent_ground_definition.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "-I", str(include), "-ccopt", f"-L{args.install_dir / 'lib'}",
         "z3ml.cmxa", *objects, test, "-o", "test_independent_ground_definition"],
        cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_ground_definition")], cwd=output,
        timeout=args.timeout, env=env)
    test = "test_independent_definition_document.ml"
    shutil.copyfile(ROOT / "tools" / test, output / test)
    run(["ocamlfind", "ocamlopt", "-warn-error", "+a", "-package", "zarith,unix",
         "-linkpkg", "-I", str(include), "-ccopt", f"-L{args.install_dir / 'lib'}",
         "z3ml.cmxa", *objects, test, "-o", "test_independent_definition_document"],
        cwd=output, timeout=args.timeout)
    run([str(output / "test_independent_definition_document")], cwd=output,
        timeout=args.timeout, env=env)
    (output / "scope.json").write_text(json.dumps({
        "root": "Z3IndependentNative.fst", "modules": sorted(closure),
    }, indent=2) + "\n", encoding="utf-8")
    print(f"Built {output / 'checker'}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fstar", type=Path, required=True)
    parser.add_argument("--z3-exe", type=Path, required=True)
    parser.add_argument("--z3-version", required=True)
    parser.add_argument("--install-dir", type=Path, required=True)
    parser.add_argument("--cache-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True, help="New build directory")
    parser.add_argument("--timeout", type=int, default=110, help="Timeout per command in seconds")
    args = parser.parse_args()
    if args.timeout <= 0 or args.timeout > 120:
        parser.error("--timeout must be between 1 and 120 seconds")
    build(args)


if __name__ == "__main__":
    main()
