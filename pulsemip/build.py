"""Verify the prototype with F*/Pulse (run on Linux, or through WSL)."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent


def run(args):
    print("+", " ".join(map(str, args)), flush=True)
    subprocess.run(list(map(str, args)), cwd=ROOT, check=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--fstar", type=Path, default=os.environ.get(
        "FSTAR_EXE", REPO / "build/fstar-epsilon-master-20261031/fstar-toolchain/bin/fstar.exe"))
    parser.add_argument("--z3", type=Path, default=os.environ.get(
        "Z3_EXE", REPO / "build/fstar-epsilon-master-20261031/native-install/bin/z3"))
    parser.add_argument("--verify-only", action="store_true")
    parser.add_argument("--test", action="store_true")
    args = parser.parse_args()
    output = ROOT / "_build"
    cache = output / "cache"
    cache.mkdir(parents=True, exist_ok=True)
    sources = sorted(set(
        list(ROOT.glob("*.fst")) + list(ROOT.glob("*.ml")) + list(ROOT.glob("*.py")) + [
            REPO / "fstar/Z3LinearArithmeticTheory.fst",
            REPO / "fstar/ocaml_runtime/Prims.ml",
            REPO / "fstar/ocaml_runtime/fStar_List_Tot_Base.ml",
        ]))
    hashes = {str(path.relative_to(REPO)): hashlib.sha256(path.read_bytes()).hexdigest()
              for path in sources}
    version = subprocess.check_output([str(args.z3), "-version"], text=True)
    match = re.search(r"Z3 version (\d+\.\d+\.\d+)", version)
    if not match:
        raise RuntimeError(f"Cannot determine Z3 version: {version}")
    common = [
        args.fstar, "--warn_error", "@1..999", "--cache_checked_modules",
        "--cache_dir", cache, "--include", cache, "--include", ROOT,
        "--include", REPO / "fstar", "--smt", args.z3, "--z3version", match.group(1),
    ]
    for source in [
        REPO / "fstar/Z3LinearArithmeticTheory.fst",
        ROOT / "PulseMip.Rational.fst",
        ROOT / "PulseMip.Model.fst",
        ROOT / "PulseMip.Certificate.fst",
        ROOT / "PulseMip.Linear.fst",
        ROOT / "PulseMip.Search.fst",
        ROOT / "PulseMip.Solver.fst",
    ]:
        run([*common, source])
    if args.verify_only:
        return
    generated = output / "generated"
    generated.mkdir(exist_ok=True)
    run([*common, "--codegen", "OCaml", "--custard_split", "--odir", generated,
         "--custard_entry", "PulseMip.Solver.solve",
         "--custard_entry", "PulseMip.Certificate.accepts",
         "--custard_entry", "PulseMip.Certificate.certify",
         ROOT / "PulseMip.Solver.fst"])
    shutil.copy2(REPO / "fstar/ocaml_runtime/Prims.ml", generated / "prims.ml")
    shutil.copy2(REPO / "fstar/ocaml_runtime/fStar_List_Tot_Base.ml", generated / "fStar_List_Tot_Base.ml")
    run(["ocamlfind", "ocamlopt", "-package", "zarith", "-c", generated / "prims.ml"])
    files = sorted(path for path in generated.glob("*.ml") if path.name != "prims.ml")
    order = subprocess.check_output(
        ["ocamlfind", "ocamldep", "-sort", *map(str, files)], cwd=ROOT, text=True).split()
    run(["ocamlfind", "ocamlopt", "-package", "zarith", "-I", generated,
         "-warn-error", "+a", "-open", "Prims", "-a", generated / "prims.cmx", *order,
         "-o", output / "pulsemip.cmxa"])
    run(["ocamlfind", "ocamlopt", "-package", "zarith", "-I", generated,
         "-c", ROOT / "main.ml", "-o", output / "main.cmx"])
    run(["ocamlfind", "ocamlopt", "-package", "zarith", "-linkpkg", "-I", generated,
         output / "pulsemip.cmxa", output / "main.cmx", "-o", output / "pulsemip"])
    if args.test:
        run(["ocamlfind", "ocamlopt", "-package", "zarith", "-I", generated,
             "-c", ROOT / "test_certificates.ml", "-o", output / "test_certificates.cmx"])
        run(["ocamlfind", "ocamlopt", "-package", "zarith", "-linkpkg", "-I", generated,
             output / "pulsemip.cmxa", output / "test_certificates.cmx",
             "-o", output / "test_certificates"])
        run([output / "test_certificates"])
        run([sys.executable, ROOT / "test_solver.py"])
    if hashes != {str(path.relative_to(REPO)): hashlib.sha256(path.read_bytes()).hexdigest()
                  for path in sources}:
        raise RuntimeError("Source files changed during verification/build")
    metadata = {
        "source_files_sha256": hashes,
        "fstar": subprocess.check_output([str(args.fstar), "--version"], text=True).strip(),
        "z3": version.strip(),
        "ocaml": subprocess.check_output(["ocamlopt", "-version"], text=True).strip(),
        "zarith": subprocess.check_output(
            ["ocamlfind", "query", "-format", "%v", "zarith"], text=True).strip(),
        "executable_sha256": hashlib.sha256((output / "pulsemip").read_bytes()).hexdigest(),
        "tests_passed": args.test,
    }
    (output / "build-info.json").write_text(json.dumps(metadata, indent=2) + "\n")


if __name__ == "__main__":
    main()
