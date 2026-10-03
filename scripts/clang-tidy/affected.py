#!/usr/bin/env python3
# Copyright (c) 2026 Microsoft Corporation
# SPDX-License-Identifier: MIT
"""Select PR translation units using dependency scans of both revisions."""
import argparse
import functools
import hashlib
import json
import pathlib
import re
import shlex
import subprocess
import tempfile

VERSION = "21.1.8"


@functools.cache
def file_key(path, source, build):
    path = pathlib.Path(path).resolve()
    # Build directories can be inside the checkout; test them first.
    for prefix, root in [("build", build), ("source", source)]:
        try:
            return prefix + "/" + path.relative_to(root.resolve()).as_posix()
        except ValueError:
            pass
    return "external/" + path.as_posix()


def compilation_units(source, build, pattern=r"/src/"):
    units = {}
    for entry in json.loads((build / "compile_commands.json").read_text()):
        path = (pathlib.Path(entry["directory"]) / entry["file"]).resolve()
        if re.search(pattern, str(path)):
            key = file_key(path, source, build)
            if key.startswith("external/"):
                raise ValueError(f"translation unit outside the checkout and build: {path}")
            units.setdefault(key, []).append({**entry, "file": str(path)})
    if not units:
        raise ValueError("no translation units in the compilation database")
    return units


def command_signatures(units, source, build):
    def normalize(value):
        return value.replace(str(build.resolve()), "<build>").replace(str(source.resolve()), "<source>")
    return {key: {normalize(json.dumps([entry["directory"],
                    entry.get("arguments") or shlex.split(entry["command"])]))
                  for entry in entries}
            for key, entries in units.items()}


def scan_dependencies(scanner, units, source, build, jobs):
    with tempfile.TemporaryDirectory(prefix="z3-dependencies-") as tmp:
        database, output = pathlib.Path(tmp) / "commands.json", pathlib.Path(tmp) / "dependencies.json"
        database.write_text(json.dumps([entry for entries in units.values() for entry in entries]))
        subprocess.run([scanner, f"-compilation-database={database}", "-format=experimental-full",
                        "-j", str(jobs), "-o", str(output)], check=True)
        result = json.loads(output.read_text())
    if result["modules"]:
        raise ValueError("unexpected C++ modules in the dependency scan")
    dependencies = {}
    for unit in result["translation-units"]:
        for command in unit["commands"]:
            key = file_key(command["input-file"], source, build)
            dependencies.setdefault(key, set()).update(
                file_key(path, source, build) for path in command["file-deps"])
    if dependencies.keys() != units.keys() or any(key not in deps for key, deps in dependencies.items()):
        raise ValueError("incomplete dependency scan")
    return dependencies


def configuration_changed(changed):
    return any(pathlib.PurePosixPath(path).name in {"CMakeLists.txt", ".clang-tidy"} or
               path.endswith(".cmake") or path.startswith(("cmake/", "scripts/clang-tidy/",
                   ".github/workflows/ast-order-warning-")) for path in changed)


def select_units(base, head, base_deps, head_deps, changed, base_build, head_build):
    changed_keys = {"source/" + path for path in changed}
    # Generated headers/sources are not in git diff. Compare their contents too.
    generated = {dep for deps in [*base_deps.values(), *head_deps.values()]
                 for dep in deps if dep.startswith("build/")}
    for key in generated:
        before, after = base_build / key[6:], head_build / key[6:]
        if not before.is_file() or not after.is_file() or before.read_bytes() != after.read_bytes():
            changed_keys.add(key)
    affected = base.keys() ^ head.keys()
    for graph in [base_deps, head_deps]:
        affected.update(key for key, deps in graph.items() if key in changed_keys or deps & changed_keys)
    # Check the counterpart even when only one revision includes the header.
    return sorted(affected & base.keys()), sorted(affected & head.keys())


def selection_id(plan):
    return hashlib.sha256(json.dumps(plan, sort_keys=True).encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for side in ["base", "head"]:
        parser.add_argument(f"--{side}-source", required=True, type=pathlib.Path)
        parser.add_argument(f"--{side}-build", required=True, type=pathlib.Path)
    parser.add_argument("--clang-scan-deps", default="clang-scan-deps-21")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--output", required=True, type=pathlib.Path)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    version = subprocess.check_output([args.clang_scan_deps, "--version"], text=True)
    if not re.search(r"version " + re.escape(VERSION) + r"\b", version):
        parser.error(f"expected clang-scan-deps {VERSION}, got {version.strip()}")
    base_sha, head_sha = [subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"],
                                                text=True).strip()
                          for root in [args.base_source, args.head_source]]
    # The PR merge checkout has depth 2, including its base parent. Disabling
    # rename detection treats moves as deletion + addition on the two sides.
    changed = subprocess.check_output(["git", "-C", str(args.head_source), "diff", "--name-only",
                                       "--no-renames", "-z", base_sha, head_sha]).decode().split("\0")[:-1]
    base = compilation_units(args.base_source, args.base_build)
    head = compilation_units(args.head_source, args.head_build)
    before = command_signatures(base, args.base_source, args.base_build)
    after = command_signatures(head, args.head_source, args.head_build)
    full = configuration_changed(changed) or any(before[key] != after[key] for key in before.keys() & after.keys())
    if full:
        selected_base, selected_head = sorted(base), sorted(head)
    else:
        base_deps = scan_dependencies(args.clang_scan_deps, base, args.base_source, args.base_build, args.jobs)
        head_deps = scan_dependencies(args.clang_scan_deps, head, args.head_source, args.head_build, args.jobs)
        selected_base, selected_head = select_units(base, head, base_deps, head_deps, changed,
                                                   args.base_build, args.head_build)
    plan = {"schema_version": 1, "mode": "full" if full else "affected",
            "base_sha": base_sha, "head_sha": head_sha,
            "base": {"sources": selected_base, "total": len(base)},
            "head": {"sources": selected_head, "total": len(head)}}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(plan, indent=2) + "\n")
    print("Full scan: build configuration, compiler commands, or checker changed." if full else
          "Selected changed sources and dependents using both revisions.")
    print(f"Base: {len(selected_base)}/{len(base)} translation units; "
          f"PR: {len(selected_head)}/{len(head)} translation units")


if __name__ == "__main__":
    main()
