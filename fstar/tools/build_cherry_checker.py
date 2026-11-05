"""Verify and build the standalone C/C++ checker with a Cherry-capable F*."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]


def run(command, **kwargs):
    command = [str(arg) for arg in command]
    print("+", shlex.join(command), flush=True)
    return subprocess.run(command, check=True, cwd=ROOT, **kwargs)


def failure_stubs(source):
    declarations = re.findall(
        r"^extern (\w+) (Z3Native_fail__\w+)\(cherry_string\);$", source, re.MULTILINE
    )
    if not declarations:
        raise RuntimeError("Cherry extraction did not declare the native failure interface")
    return "".join(
        f'extern "C" {result} {name}(cherry_string message) {{ checker::fail(message); }}\n'
        for result, name in sorted(set(declarations))
    )


def build(args):
    if platform.system() != "Linux" or platform.machine() not in ("x86_64", "aarch64"):
        raise RuntimeError("The Cherry checker requires Linux x86-64 or AArch64 (use WSL on Windows)")
    output = args.build_dir.resolve()
    args.fstar = args.fstar.resolve()
    cache = (args.cache_dir or output / "cache").resolve()
    generated = output / "generated"
    for path in (output, cache, generated):
        path.mkdir(parents=True, exist_ok=True)
    install = args.z3_install.resolve()
    z3 = install / "bin/z3"
    library = install / "lib/libz3.a"
    if not z3.is_file() or not library.is_file():
        raise RuntimeError(f"Build and install static Z3 first; expected {z3} and {library}")
    version = run([z3, "-version"], capture_output=True, text=True).stdout
    match = re.search(r"\bZ3 version (\d+\.\d+\.\d+)\b", version)
    if not match:
        raise RuntimeError(f"Cannot determine the installed Z3 version: {version}")
    gcc = run([args.cc, "-dumpfullversion"], capture_output=True, text=True).stdout.strip()
    compiler = run([args.cc, "--version"], capture_output=True, text=True).stdout
    if not gcc or int(gcc.split(".")[0]) < 15 or "clang" in compiler.lower():
        raise RuntimeError("Cherry requires GCC 15+ for guaranteed tail calls")
    fstar_version = run([args.fstar, "--version"], capture_output=True, text=True).stdout
    runtime = Path(run([args.fstar, "--locate_lib"], capture_output=True, text=True).stdout.strip()) / "ulib/c"
    if not (runtime / "cherry.c").is_file():
        raise RuntimeError(f"Missing Cherry runtime: {runtime / 'cherry.c'}")
    common = [
        args.fstar, "--message_format", "human", "--timing", "--warn_error", "@1..999",
        "--cache_dir", cache, "--include", cache, "--include", ROOT,
        "--smt", z3, "--z3version", match.group(1),
    ]
    manifest = json.loads((ROOT / "tools/checker_modules.json").read_text(encoding="utf-8"))
    modules = manifest["modules"] + manifest["cherry_modules"] + ["Z3Cherry.fst"]
    if args.run_tests:
        modules += manifest["tests"] + ["Z3CherryTests.fst"]
    for module in modules:
        run(common + ["--cache_checked_modules", ROOT / module])
    entries = ["Z3Cherry.marshal", "Z3Cherry.check", "Z3Cherry.diagnose",
               "Z3Cherry.constructor_op", "Z3Cherry.recognizer_op",
               "Z3Cherry.accessor_op", "Z3Cherry.rational_op"]
    if args.run_tests:
        entries.append("Z3CherryTests.run")
    extraction = [
        # The pinned compiler warns about monomorphic C ABI names. The bridge
        # compiles against this very header, never a previously generated ABI.
        "--warn_error", "-377", "--codegen", "Cherry",
        "--custard_monomorphize_types", "true",
        "--custard_extern_type", "Z3Native.ast=Z3_ast@z3.h",
        "--custard_extern_type", "Z3Native.native_sort=Z3_sort@z3.h",
        "--odir", generated, "-o", generated / "Z3Cherry.c",
    ]
    for entry in entries:
        extraction += ["--custard_entry", entry]
    run(common + extraction + [ROOT / ("Z3CherryTests.fst" if args.run_tests else "Z3Cherry.fst")])
    (generated / "native_failures.inc").write_text(
        failure_stubs((generated / "Z3Cherry.c").read_text(encoding="utf-8")), encoding="utf-8"
    )
    includes = ["-I", generated, "-I", runtime, "-I", install / "include",
                "-I", ROOT / "cherry_runtime"]
    flags = ["-O2", "-g", "-DCHERRY_DEBUG", "-fexceptions"]
    if args.sanitize:
        flags += ["-O1", "-fsanitize=address,undefined", "-fno-omit-frame-pointer"]
    objects = []
    for source, cc, language in (
        (ROOT / "cherry_runtime/kernel.c", args.cc, "-std=c11"),
        (runtime / "cherry.c", args.cc, "-std=c11"),
        (ROOT / "cherry_runtime/native.cpp", args.cxx, "-std=c++20"),
    ):
        target = output / (source.stem + ".o")
        warnings = ["-Wall", "-Wextra", "-Werror"] if language == "-std=c++20" else []
        run([cc, language, *flags, *warnings, *includes, "-c", source, "-o", target])
        objects.append(target)
    for name, source in [("checker", "main.cpp")] + (
        [("checker-tests", "tests.cpp")] if args.run_tests else []
    ):
        run([args.cxx, "-std=c++20", *flags, "-Wall", "-Wextra", "-Werror", *includes,
             ROOT / "cherry_runtime" / source, *objects, library, "-lpthread", "-ldl", "-lm",
             "-o", output / name])
    if args.run_tests:
        run([output / "checker-tests"])
        environment = os.environ.copy()
        environment["Z3_FSTAR_CHECKER"] = str(output / "checker")
        environment.pop("Z3_FSTAR_WSL_DISTRO", None)
        run([sys.executable, ROOT / "tools/test_native_checker.py"], env=environment)
    metadata = {
        "backend": "Cherry", "fstar": fstar_version.strip(), "z3": version.strip(),
        "cc": compiler.strip(),
        "cxx": run([args.cxx, "--version"], capture_output=True, text=True).stdout.strip(),
        "commit": run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip(),
        "system": platform.platform(), "sanitizers": args.sanitize,
        "sha256": hashlib.sha256((output / "checker").read_bytes()).hexdigest(),
    }
    (output / "build.json").write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    print(f"Cherry checker: {output / 'checker'}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fstar", type=Path, required=True)
    parser.add_argument("--z3-install", type=Path, required=True)
    parser.add_argument("--build-dir", type=Path, required=True)
    parser.add_argument("--cache-dir", type=Path)
    parser.add_argument("--cc", default="gcc-15")
    parser.add_argument("--cxx", default="g++-15")
    parser.add_argument("--run-tests", action="store_true")
    parser.add_argument("--sanitize", action="store_true")
    args = parser.parse_args()
    try:
        build(args)
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"ERROR {error}\n")


if __name__ == "__main__":
    main()
