"""Verify and Cherry-extract the SQL rewrite kernel; link a native Z3 solver."""

import argparse
import hashlib
import json
import platform
import re
import subprocess
import tarfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCES = ROOT / "sql_solver"
OPCODES = {
    "sql.empty": 1, "sql.filter": 2, "sql.project": 3, "sql.unionAll": 4,
    "sql.cross": 5, "sql.join": 6, "sql.count": 7, "sql.countOne": 8,
    "sql.countValue": 9, "sql.countWhen": 10, "sql.addCounts": 11,
    "sql.identity": 20, "sql.mapping": 21, "sql.compose": 22,
    "sql.true": 30, "sql.false": 31, "sql.predicate": 32, "sql.and": 33,
    "sql.preimage": 34, "sql.notNull": 35,
}


def run(command, **kwargs):
    command = [str(x) for x in command]
    print("+", " ".join(command), flush=True)
    return subprocess.run(command, check=True, **kwargs)


def signature_header():
    text = (SOURCES / "signature.smt2").read_text(encoding="utf-8")
    declarations = ['static void initialize_signature(bridge& b) {']
    for name in re.findall(r"\(declare-sort (\S+) 0\)", text):
        declarations.append(f'    b.add_sort("{name}");')
    for name, domain, range_ in re.findall(
            r"\(declare-fun (\S+) \(([^)]*)\) (\S+)\)", text):
        args = ", ".join(json.dumps(s) for s in domain.split())
        declarations.append(
            f'    b.declare("{name}", {OPCODES.get(name, 0)}, {{{args}}}, "{range_}");')
    declarations.append("}")
    return 'static char const* signature_text = R"SQL(' + text + ')SQL";\n' + "\n".join(declarations)


def build(args):
    if platform.system() != "Linux" or platform.machine() not in ("x86_64", "aarch64"):
        raise RuntimeError("Cherry requires Linux x86-64/AArch64; use WSL on Windows")
    args.fstar = args.fstar.resolve()
    install = args.z3_install.resolve()
    out = args.build_dir.resolve()
    generated, cache = out / "generated", out / "cache"
    for d in (out, generated, cache):
        d.mkdir(parents=True, exist_ok=True)
    z3, library = install / "bin/z3", install / "lib/libz3.a"
    if not z3.is_file() or not library.is_file():
        raise RuntimeError(f"Expected installed Z3 executable and static library under {install}")
    gcc = run([args.cc, "-dumpfullversion"], capture_output=True, text=True).stdout.strip()
    if int(gcc.split(".")[0]) < 15:
        raise RuntimeError("Cherry requires GCC 15+")
    version = run([z3, "--version"], capture_output=True, text=True).stdout.strip()
    backend_version = re.search(r"Z3 version (\S+)", version).group(1)
    fstar_version = run([args.fstar, "--version"], capture_output=True, text=True).stdout.strip()
    runtime = Path(run([args.fstar, "--locate_lib"], capture_output=True, text=True).stdout.strip()) / "ulib/c"
    common = [args.fstar, "--smt", z3, "--z3version", backend_version,
              "--include", ROOT, "--cache_dir", cache, "--cache_checked_modules",
              "--already_cached", "Prims,FStar", "--warn_error", "@1..999"]
    modules = ["Sql.Core.fst", "Sql.Query.fst", "Sql.Laws.fst", "Sql.Optimize.fst",
               "Sql.Native.fsti", "Sql.Cherry.fst"]
    for module in modules:
        run([*common, ROOT / module])
    run([*common, "--warn_error", "-377", "--codegen", "Cherry",
         "--custard_entry", "Sql.Cherry.rewrite_native",
         "--custard_monomorphize_types", "true",
         "--custard_extern_type", "Sql.Native.term=Z3_ast@z3.h",
         "--odir", generated, "-o", generated / "SqlCherry.c", ROOT / "Sql.Cherry.fst"])
    (generated / "signature.inc").write_text(signature_header(), encoding="utf-8")
    flags = ["-O2", "-g", "-DCHERRY_DEBUG", "-fexceptions"]
    if args.sanitize:
        flags += ["-O1", "-fsanitize=address,undefined", "-fno-omit-frame-pointer"]
    includes = ["-I", generated, "-I", runtime, "-I", install / "include"]
    objects = []
    for source in (SOURCES / "kernel.c", runtime / "cherry.c"):
        obj = out / (source.stem + ".o")
        run([args.cc, "-std=c11", *flags, *includes, "-c", source, "-o", obj])
        objects.append(obj)
    exe = out / "sql-solver"
    run([args.cxx, "-std=c++20", *flags, "-Wall", "-Wextra", "-Werror", *includes,
         SOURCES / "main.cpp", *objects, library, "-lpthread", "-ldl", "-lm", "-o", exe])
    if args.run_tests:
        run([exe, "--self-test"])
        run(["python3", ROOT / "tools/test_sql_solver.py", "--solver", exe])
    (out / "build.json").write_text(json.dumps({
        "backend": "Cherry", "fstar": fstar_version, "z3": version,
        "gcc": gcc, "sanitizers": args.sanitize,
        "sha256": hashlib.sha256(exe.read_bytes()).hexdigest(),
    }, indent=2) + "\n", encoding="utf-8")
    archive = out / f"sql-solver-linux-{platform.machine()}.tar.gz"
    license_ = args.fstar.parent.parent / "LICENSE"
    if not license_.is_file():
        raise RuntimeError(f"Missing F* runtime license: {license_}")
    with tarfile.open(archive, "w:gz") as package:
        for source, name in [
                (exe, "sql-solver"), (out / "build.json", "build.json"),
                (SOURCES / "signature.smt2", "signature.smt2"),
                (SOURCES / "README.md", "README.md"),
                (ROOT.parent / "LICENSE.txt", "LICENSE-Z3.txt"),
                (license_, "LICENSE-FSTAR")]:
            package.add(source, arcname=f"sql-solver/{name}")
        for example in sorted((SOURCES / "examples").glob("*.smt2")):
            package.add(example, arcname=f"sql-solver/examples/{example.name}")
    checksum = hashlib.sha256(archive.read_bytes()).hexdigest()
    archive.with_suffix(archive.suffix + ".sha256").write_text(
        f"{checksum}  {archive.name}\n", encoding="ascii")
    print(f"SQL solver: {exe}", flush=True)
    print(f"Package: {archive}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fstar", required=True, type=Path)
    parser.add_argument("--z3-install", required=True, type=Path)
    parser.add_argument("--build-dir", required=True, type=Path)
    parser.add_argument("--cc", default="gcc-15")
    parser.add_argument("--cxx", default="g++-15")
    parser.add_argument("--run-tests", action="store_true")
    parser.add_argument("--sanitize", action="store_true")
    args = parser.parse_args()
    try:
        build(args)
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"ERROR: {error}\n")


if __name__ == "__main__":
    main()
