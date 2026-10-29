#!/usr/bin/env python3
"""Strictly verify all invertibility proofs and test their extracted definitions."""

import argparse
import contextlib
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import tempfile


MODULES = (
    "Z3BvTheory", "Z3BvRewriter", "Z3BvInvertibility",
    "Z3BvInvertibilityConditions", "Z3BvInvertibilityProofs",
    "Z3BvInvertibilityBits", "Z3BvInvertibilitySigned",
    "Z3BvInvertibilityArithmetic", "Z3BvInvertibilityDivision",
    "Z3BvInvertibilityDividend", "Z3BvInvertibilityShifts",
    "Z3BvInvertibilityRemainder", "Z3BvInvertibilityLogical",
    "Z3BvInvertibilityCarry", "Z3BvInvertibilityFactors",
    "Z3BvInvertibilityMultiply", "Z3BvInvertibilityFinal",
    "Z3BvInvertibilityComplete",
)
EXTRACTED = ("Z3BvTheory", "Z3BvInvertibility", "Z3BvInvertibilityConditions")


def executable(value):
    found = shutil.which(value)
    if found:
        return str(Path(found).resolve())
    raise argparse.ArgumentTypeError(f"executable not found: {value}")


def run(command, cwd, log, **kwargs):
    print(shlex.join(map(str, command)), flush=True)
    with log.open("ab") as output:
        output.write(("\n$ " + shlex.join(map(str, command)) + "\n").encode())
        output.flush()
        result = subprocess.run(command, cwd=cwd, stdout=output,
                                stderr=subprocess.STDOUT, **kwargs)
    if result.returncode:
        print(log.read_text(encoding="utf-8", errors="replace"))
        raise subprocess.CalledProcessError(result.returncode, command)


def native_test(args, root, work):
    native = work / "native"
    native.mkdir()
    for name in ("prims.ml", "fStar_UInt.ml"):
        shutil.copy2(root / "ocaml_runtime" / name, native / name)
    for module in EXTRACTED:
        shutil.copy2(work / "extracted" / f"{module}.ml", native)
    shutil.copy2(root / "tools" / "test_bv_invertibility.ml", native)
    if args.wsl:
        directory = subprocess.check_output(
            ["wsl", "--exec", "wslpath", "-a", "-u", str(native)],
            text=True).strip()
        command = ["wsl", "--exec", "bash", "-s"]
    else:
        directory = str(native)
        command = ["bash", "-s"]
    environment = ""
    if args.opam_switch:
        environment = (
            'export PATH="$HOME/bin:$PATH"\n'
            f'eval "$(opam env --switch={shlex.quote(args.opam_switch)})"\n'
        )
    script = f"""set -euo pipefail
{environment}cd {shlex.quote(directory)}
install={shlex.quote(args.ocaml_install)}
if [[ "$install" == '~/'* ]]; then install="$HOME/${{install:2}}"; fi
test -f "$install/lib/ocaml/z3/z3ml.cmxa"
export LD_LIBRARY_PATH="$install/lib:${{LD_LIBRARY_PATH:-}}"
ocamlfind ocamlopt -warn-error +a -package zarith,unix -linkpkg \\
  -I "$install/lib/ocaml/z3" -ccopt "-L$install/lib" z3ml.cmxa \\
  prims.ml fStar_UInt.ml Z3BvTheory.ml Z3BvInvertibility.ml \\
  Z3BvInvertibilityConditions.ml test_bv_invertibility.ml -o invertibility-tests
./invertibility-tests {args.max_width}
"""
    log = work / "native-tests.log"
    run(command, root, log, input=script.encode())
    print(log.read_text(encoding="utf-8"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fstar", required=True, type=executable)
    parser.add_argument("--z3", required=True, type=executable,
                        help="Z3 executable built and installed from this checkout")
    parser.add_argument("--verify-only", action="store_true")
    parser.add_argument("--ocaml-install",
                        help="native Z3 installation prefix, inside WSL with --wsl")
    parser.add_argument("--wsl", action="store_true")
    parser.add_argument("--opam-switch")
    parser.add_argument("--max-width", type=int, choices=range(1, 9), default=8)
    parser.add_argument("--output-dir", type=Path,
                        help="retain logs and artifacts in a fresh child directory")
    args = parser.parse_args()
    if not args.verify_only and not args.ocaml_install:
        parser.error("--ocaml-install is required unless --verify-only is set")
    root = Path(__file__).resolve().parents[1]
    version = subprocess.check_output([args.z3, "--version"], text=True).strip()
    match = re.match(r"Z3 version (\d+\.\d+\.\d+)", version)
    if not match:
        parser.error(f"unexpected Z3 version: {version}")
    print(version, flush=True)
    if args.output_dir:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        work = Path(tempfile.mkdtemp(prefix="run-", dir=args.output_dir.resolve()))
        workspace = contextlib.nullcontext(str(work))
    else:
        workspace = tempfile.TemporaryDirectory(prefix="z3-bv-invertibility-")
    with workspace as directory:
        work = Path(directory).resolve()
        print(f"Artifacts: {work}", flush=True)
        cache = work / "checked"
        cache.mkdir()
        common = [args.fstar, "--smt", args.z3, "--z3version", match[1],
                  "--warn_error", "@1..999", "--cache_dir", str(cache)]
        for module in MODULES:
            run(common + ["--cache_checked_modules", f"{module}.fst"],
                root, work / "verification.log")
        print("All 160 arbitrary-width invertibility conditions verified.", flush=True)
        if not args.verify_only:
            extracted = work / "extracted"
            extracted.mkdir()
            run(common + ["--codegen", "OCaml", "--include", str(cache),
                          "--odir", str(extracted), "--extract", " ".join(EXTRACTED),
                          "Z3BvInvertibilityConditions.fst"],
                root, work / "extraction.log")
            native_test(args, root, work)


if __name__ == "__main__":
    main()
