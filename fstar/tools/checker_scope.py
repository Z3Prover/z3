"""Select the F* modules verified by the checker-only and full native checker builds."""

import argparse
import json
from pathlib import Path
import re
import shlex
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]


def dependency_files(output, directory):
    """Names of the sources in `directory` listed by F*'s `--dep full` output."""
    output = output.replace("\r\n", "\n")
    directory = Path(directory).resolve()
    names = set()
    for variable in ("ALL_FST_FILES", "ALL_FSTI_FILES"):
        match = re.search(rf"^{variable}=((?:.*\\\n)*.*)$", output, re.MULTILINE)
        if not match:
            raise RuntimeError(f"F* dependency output lacks {variable}")
        for entry in match.group(1).replace("\\\n", " ").split():
            path = directory / entry
            if path.resolve().parent == directory:
                names.add(path.name)
    return names


def dependency_command(fstar, roots):
    """F* dependency discovery takes no verification flags: they only make it fail on library paths."""
    return [fstar, "--dep", "full", *roots]


def dependency_closure(command, directory=ROOT):
    command = [str(arg) for arg in command]
    print("+", shlex.join(command), file=sys.stderr, flush=True)
    result = subprocess.run(command, cwd=directory, capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"F* dependency analysis failed:\n{result.stdout}{result.stderr}")
    return dependency_files(result.stdout, directory)


def backend_lists(manifest, backend):
    if backend == "cherry":
        return (manifest["modules"] + manifest["cherry_modules"] + ["Z3Cherry.fst"],
                manifest["tests"] + ["Z3CherryTests.fst"])
    return manifest["modules"], manifest["tests"]


def select(manifest, backend, full, closure, roots):
    """Production modules and tests to verify, in manifest order."""
    production, tests = backend_lists(manifest, backend)
    registered = set(production + manifest["cherry_modules"])
    unregistered = sorted(closure - registered)
    if unregistered:
        raise RuntimeError("Checker dependencies are not registered production modules: "
                           + ", ".join(unregistered))
    outside = [root for root in roots if root not in closure]
    if outside:
        raise RuntimeError("Checker roots are outside their F* dependency closure: "
                           + ", ".join(outside))
    if full:
        return production, tests
    return [module for module in production if module in closure], []


def extraction_entries(manifest, closure, full):
    return [module for module in manifest["modules"]
            if (full or module in closure) and not module.endswith(".fsti")]


def write_report(path, manifest, backend, full, fstar_version, roots, modules, tests):
    production, all_tests = backend_lists(manifest, backend)
    selected = modules + tests
    report = {
        "source_sha": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "backend": backend,
        "mode": "full" if full else "checker",
        "verification_scope": ("all registered production modules and tests" if full else
                               "F* dependency closure of the checker roots; no F* tests"),
        "native_tests": full,
        "fstar": fstar_version.strip(),
        "roots": roots,
        "selected_modules": selected,
        "selected_count": len(selected),
        "registered_not_selected": [m for m in production + all_tests if m not in selected],
    }
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fstar", type=Path, required=True)
    parser.add_argument("--backend", choices=("ocaml", "cherry"), required=True)
    parser.add_argument("--full", action="store_true")
    parser.add_argument("--report", type=Path)
    parser.add_argument("roots", nargs="+")
    args = parser.parse_args()
    try:
        manifest = json.loads((ROOT / "tools/checker_modules.json").read_text(encoding="utf-8"))
        closure = dependency_closure(dependency_command(args.fstar, args.roots))
        modules, tests = select(manifest, args.backend, args.full, closure, args.roots)
        if args.report:
            version = subprocess.check_output([str(args.fstar), "--version"], text=True)
            write_report(args.report, manifest, args.backend, args.full, version,
                         args.roots, modules, tests)
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"ERROR {error}\n")
    print(json.dumps({"modules": modules, "tests": tests,
                      "entries": extraction_entries(manifest, closure, args.full)}))


if __name__ == "__main__":
    main()
