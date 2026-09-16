#!/usr/bin/env python3
"""Reproducible, single-query nseq ablations; Python standard library only.

See resplit_ablation.md. No builds, downloads, or benchmark campaigns happen
implicitly. 'prepare' never invokes a solver; 'run' requires a build record.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import csv
from dataclasses import dataclass
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import time

CONFIG = Path(__file__).with_suffix(".json")
DECIDED = {"sat", "unsat"}
STATUSES = ("sat", "unsat", "unknown", "timeout", "error")
RUN_FIELDS = ["id", "path", "family", "category", "expected", "repeat", "config",
              "status", "seconds", "reason", "returncode"]

# Keep the schema contract aligned with Bench's importer. The actual argv
# vectors are always expanded from the frozen source JSON.
DEFAULT_STUDY = {
    "smt.string_solver": "nseq", "tactic.default_tactic": "", "model_validate": True,
    "smt.random_seed": 0, "sat.random_seed": 0,
    **{"smt.nseq." + k: v for k, v in {
        "equation_abstraction": False, "reverse_retry": True,
        "monadic_leaf": True, "regex_parikh": True, "parikh": False, "abelian": False,
        "monadic_split": False, "monadic_landing": False, "monadic_leaf_refute": False,
        "monadic_leaf_root": True, "monadic_leaf_budget": 300000,
        "monadic_leaf_budget_refute": 30000, "monadic_leaf_budget_root": 50000,
        "regex_parikh_mod": 5, "regex_precheck": True, "view_length_constraints": True,
        "regex_factorization_eager": False, "regex_factorization_threshold": 1,
        "regex_dynamic_decomposition": True, "eager": True, "max_depth": 0, "max_nodes": 0,
        "block_compression": 1, "exploration_budget": 512, "signature": False,
        "fine_wilf": False, "axiomatize_diseq": False, "harvest": 0,
    }.items()},
}
DEFAULT_FLIPS = {
    "z3-tacas": {},
    "z3-tacas-no-monadic-leaf": {"smt.nseq.monadic_leaf": False},
    "z3-tacas-no-regex-parikh": {"smt.nseq.regex_parikh": False},
    "z3-tacas-equation-abstraction": {"smt.nseq.equation_abstraction": True},
    "z3-tacas-no-factorization": {"smt.nseq.regex_factorization_threshold": 0},
    "z3-tacas-no-reversal": {"smt.nseq.reverse_retry": False},
    "z3-tacas-abelian": {"smt.nseq.abelian": True},
}


def validate_default_matrix(matrix):
    if set(matrix) != {"schema", "baseline", "common", "configurations"}:
        raise ValueError("schema 2 requires baseline, common and configurations only")
    if matrix["baseline"] != "z3-tacas" or matrix["common"] != DEFAULT_STUDY:
        raise ValueError("schema 2 baseline must preserve the frozen native defaults")
    if any(type(matrix["common"][k]) is not type(v) for k, v in DEFAULT_STUDY.items()):
        raise ValueError("schema 2 baseline parameter types differ from defaults")
    entries = matrix["configurations"]
    if not isinstance(entries, list) or len(entries) != 7:
        raise ValueError("schema 2 requires exactly seven configurations")
    if [e.get("name") for e in entries if isinstance(e, dict)] != list(DEFAULT_FLIPS):
        raise ValueError("schema 2 requires the canonical seven-arm order and names")
    for entry in entries:
        expected = DEFAULT_FLIPS[entry["name"]]
        if set(entry) != {"name", "overrides"} or entry["overrides"] != expected:
            raise ValueError("schema 2 requires exactly the declared single-option flip")
        if any(type(entry["overrides"][k]) is not type(v) for k, v in expected.items()):
            raise ValueError("schema 2 flip parameter types differ from the contract")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args])


@dataclass(frozen=True)
class Atom:
    kind: str
    text: str


def symbol(node, value=None):
    return isinstance(node, Atom) and node.kind == "symbol" and (
        value is None or node.text == value)


def parse(text):
    """SMT-LIB lexer + iterative S-expression reader, preserving command spans.

    Strings use SMT-LIB doubled quotes, not C backslash escapes. Quoted symbols
    are never mistaken for operators. Comments end at newline, including CR.
    This is a structural validator, not a type checker (Z3 remains the latter).
    """
    stack, commands = [], []
    i, start = 0, 0
    while i < len(text):
        c = text[i]
        if c.isspace() or c == "\ufeff":
            i += 1
            continue
        if c == ";":
            while i < len(text) and text[i] not in "\r\n":
                i += 1
            continue
        if c == "(":
            if not stack:
                start = i
            stack.append([])
            i += 1
            continue
        if c == ")":
            if not stack:
                raise ValueError("unmatched ')'")
            node = stack.pop()
            i += 1
            if stack:
                stack[-1].append(node)
            else:
                commands.append((node, start, i))
            continue
        begin = i
        if c in '"|':
            delim = c
            i += 1
            while i < len(text):
                if text[i] == delim:
                    if delim == '"' and i + 1 < len(text) and text[i + 1] == '"':
                        i += 2
                        continue
                    i += 1
                    break
                i += 1
            else:
                raise ValueError("unterminated string or quoted symbol")
            token = Atom("string" if delim == '"' else "quoted", text[begin:i])
        else:
            while i < len(text) and not text[i].isspace() and text[i] not in '();"|':
                i += 1
            token = Atom("symbol", text[begin:i])
        if not stack:
            raise ValueError("atom outside command")
        stack[-1].append(token)
    if stack:
        raise ValueError("unclosed '('")
    return commands


def nodes(root):
    pending = [root]
    while pending:
        node = pending.pop()
        yield node
        if isinstance(node, list):
            pending.extend(reversed(node))


def token_identity(commands):
    # Iterative encoding, insensitive to comments/whitespace, not to semantics.
    parts = []
    for command in commands:
        pending = [command]
        while pending:
            node = pending.pop()
            if isinstance(node, list):
                parts.append("(")
                pending.append(")")
                pending.extend(reversed(node))
            elif isinstance(node, Atom):
                parts.append(json.dumps([node.kind, node.text]))
            else:
                parts.append(node)
    return digest("".join(parts).encode())


def inspect_problem(data):
    text = data.decode("utf-8-sig")
    commands = parse(text)
    checks = [n for n, _, _ in commands if n and symbol(n[0], "check-sat")]
    if len(checks) != 1 or len(checks[0]) != 1:
        raise ValueError("requires exactly one plain check-sat")
    kept, formula, removed, assertions, declarations = [], [], [], [], {}
    expected, checked, definitions = "", False, False
    allowed = {"set-logic", "set-info", "declare-const", "declare-fun", "define-fun", "assert"}
    presentation = {"get-model", "get-value", "get-info", "get-assignment", "exit"}
    for node, begin, end in commands:
        if not node or not symbol(node[0]):
            raise ValueError("invalid command head")
        cmd = node[0].text
        if cmd == "check-sat":
            checked = True
            continue
        if cmd in presentation:
            if not checked:
                raise ValueError("presentation command before check-sat")
            removed.append(cmd)
            continue
        if checked:
            raise ValueError("state-changing command after check-sat")
        if cmd == "set-option":
            if len(node) != 3 or not symbol(node[1]) or node[1].text not in {
                    ":produce-models", ":print-success"} or not (
                    symbol(node[2], "true") or symbol(node[2], "false")):
                raise ValueError("solver/resource option in input (not silently overridden)")
            removed.append(text[begin:end])
            continue
        if cmd not in allowed:
            raise ValueError(f"unsupported/incremental command: {cmd}")
        if cmd == "set-info" and len(node) >= 2 and symbol(node[1], ":status"):
            if len(node) != 3 or not symbol(node[2]) or node[2].text not in DECIDED | {"unknown"}:
                raise ValueError("malformed :status annotation")
            if expected and expected != node[2].text:
                raise ValueError("conflicting :status annotations")
            expected = node[2].text
        if cmd == "assert":
            if len(node) != 2:
                raise ValueError("malformed assert")
            assertions.append(node[1])
        if cmd == "declare-const" and len(node) == 3 and isinstance(node[1], Atom):
            declarations[node[1]] = node[2]
        if cmd == "declare-fun" and len(node) == 4 and node[2] == [] and isinstance(node[1], Atom):
            declarations[node[1]] = node[3]
        if cmd == "define-fun":
            definitions = True
        kept.append(text[begin:end])
        if cmd != "set-info":
            formula.append(node)

    # Certify a narrow, useful fragment only. Anything with aliases, quantifiers,
    # non-String declarations, or other operators is mixed/unclassified.
    string_vars = {v for v, sort in declarations.items() if symbol(sort, "String")}

    def string_term(n):
        return all(
            (x.kind == "string" or x in string_vars) if isinstance(x, Atom) else
            bool(x) and symbol(x[0], "str.++")
            for x in term_nodes(n))

    def term_nodes(n):
        pending = [n]
        while pending:
            x = pending.pop()
            yield x
            if isinstance(x, list):
                pending.extend(x[1:])

    regex_ops = {"re.++", "re.union", "re.inter", "re.*", "re.+", "re.opt",
                 "re.comp", "re.diff", "re.range", "str.to_re"}

    def ground_regex(n):
        if symbol(n) and n.text in {"re.all", "re.allchar", "re.none"}:
            return True
        if not isinstance(n, list) or not n:
            return False
        if symbol(n[0], "str.to_re"):
            return len(n) == 2 and isinstance(n[1], Atom) and n[1].kind == "string"
        if symbol(n[0], "re.range"):
            return len(n) == 3 and all(isinstance(x, Atom) and x.kind == "string" for x in n[1:])
        if symbol(n[0]) and n[0].text in regex_ops:
            return all(ground_regex(x) for x in n[1:])
        head = n[0]
        if isinstance(head, list) and len(head) in (3, 4) and symbol(head[0], "_") and (
                symbol(head[1], "re.loop") or symbol(head[1], "re.^")):
            return all(symbol(x) and x.text.isdigit() for x in head[2:]) and (
                len(n) == 2 and ground_regex(n[1]))
        return False

    def membership_formula(n):
        if symbol(n, "true") or symbol(n, "false"):
            return True
        if not isinstance(n, list) or not n:
            return False
        if any(symbol(n[0], b) for b in ("and", "or", "not", "=>", "xor")):
            return all(membership_formula(x) for x in n[1:])
        return len(n) == 3 and symbol(n[0], "str.in_re") and string_term(n[1]) and ground_regex(n[2])

    flat = [x for a in assertions for x in nodes(a)]
    opaque = definitions or any(isinstance(x, list) and x and symbol(x[0]) and
                               x[0].text in {"let", "forall", "exists", "lambda", "match"} for x in flat)
    has_length = any(isinstance(x, list) and x and symbol(x[0], "str.len") for x in flat)
    has_equation = any(isinstance(x, list) and len(x) >= 3 and
                       (symbol(x[0], "=") or symbol(x[0], "distinct")) and
                       all(string_term(y) for y in x[1:]) for x in flat)
    try:
        pure = not definitions and len(string_vars) == len(declarations) and bool(assertions) and (
            all(membership_formula(a) for a in assertions))
    except RecursionError:
        pure = False  # deep regular expressions remain runnable, but uncertified
    category = ("unclassified" if opaque else "pure-membership" if pure else "equations-and-lengths" if has_equation and has_length
                else "equations" if has_equation else "lengths" if has_length else "unclassified")
    prepared = ("\n".join(kept) + "\n(check-sat)\n(get-info :reason-unknown)\n").encode()
    return {"expected": expected, "category": category, "removed_commands": removed,
            "formula_sha256": token_identity(formula)}, prepared


def configurations(path=CONFIG):
    spec = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(spec, dict) or spec.get("schema") not in (1, 2):
        raise ValueError("requires schema 1 (historical) or 2 (defaults)")
    if spec["schema"] == 2:
        validate_default_matrix(spec)
    result = {}
    for entry in spec["configurations"]:
        params = dict(spec["common"])
        if spec["schema"] == 1:
            params.update({param: entry[group] for group, param in spec["groups"].items()})
        params.update(entry.get("overrides", {}))
        name = entry["name"]
        if name in result or not re.fullmatch(r"[A-Za-z0-9-]+", name):
            raise ValueError("duplicate/unsafe configuration name")
        result[name] = [f"{k}={str(v).lower() if isinstance(v, bool) else v}" for k, v in sorted(params.items())]
    if spec["baseline"] not in result:
        raise ValueError("baseline missing")
    return spec, result


def source_identity(root):
    root = Path(root).resolve()
    # Include the index and working tree together; untracked files get their
    # bytes archived, rather than calling a dirty binary the pristine HEAD.
    diff = git(root, "diff", "--binary", "--no-ext-diff", "HEAD", "--")
    untracked = git(root, "ls-files", "--others", "--exclude-standard", "-z").decode().split("\0")
    extra = {}
    for rel in filter(None, untracked):
        path = root / rel
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"unsupported untracked source: {rel}")
        extra[rel] = digest(path.read_bytes())
    return {"head": git(root, "rev-parse", "HEAD").decode().strip(),
            "diff_sha256": digest(diff), "untracked_sha256": extra}, diff


def record_build(args):
    out = args.out.resolve()
    root = args.source.resolve()
    if args.native_base_sha:
        if not re.fullmatch(r"[0-9a-f]{40}", args.native_base_sha):
            raise ValueError("native base must be a full immutable SHA")
        git(root, "merge-base", "--is-ancestor", args.native_base_sha, "HEAD")
    if out.is_relative_to(root) and ".z3-agent" not in out.relative_to(root).parts:
        raise ValueError("build record must be outside source or under ignored .z3-agent")
    identity, diff = source_identity(root)
    if (diff or identity["untracked_sha256"]) and not args.allow_dirty:
        raise ValueError("dirty source: rebuild then explicitly use --allow-dirty to archive its delta")
    out.mkdir(parents=True, exist_ok=False)
    (out / "source.diff").write_bytes(diff)
    for rel in identity["untracked_sha256"]:
        target = out / "untracked" / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / rel, target)
    for name in ("CMakeCache.txt", "build.ninja"):
        source = args.build_dir / name
        if not source.is_file():
            raise ValueError(f"missing CMake/Ninja build evidence: {source}")
        shutil.copyfile(source, out / name)
    compiler_files = sorted(args.build_dir.glob("CMakeFiles/*/CMakeCXXCompiler.cmake"))
    if not compiler_files:
        raise ValueError("missing CMake compiler identification")
    compiler_evidence = {}
    for path in compiler_files:
        rel = path.relative_to(args.build_dir)
        target = out / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
        compiler_evidence[rel.as_posix()] = digest(path.read_bytes())
    version = subprocess.run([str(args.z3.resolve()), "--version"], capture_output=True, check=True)
    version_text = version.stdout.decode(errors="replace")
    if identity["head"] not in version_text:
        raise ValueError(f"binary version does not identify recorded source {identity['head']}: {version_text}")
    listing = subprocess.run([str(args.z3.resolve()), "-p"], capture_output=True, check=True, timeout=30)
    for stream in ("stdout", "stderr"):
        (out / ("parameters." + stream)).write_bytes(getattr(listing, stream))
    record = {"schema": 1, "source": str(root), "source_identity": identity,
              "native_base_sha": args.native_base_sha,
              "binary": str(args.z3.resolve()), "binary_sha256": digest(args.z3.read_bytes()),
              "version": version_text, "build_command": args.build_command,
              "parameter_listing": {"argv": [str(args.z3.resolve()), "-p"],
                                    "sha256": {s: digest(getattr(listing, s))
                                               for s in ("stdout", "stderr")}},
              "build_dir": str(args.build_dir.resolve()),
              "build_evidence": {**compiler_evidence, **{
                  n: digest((out / n).read_bytes()) for n in ("CMakeCache.txt", "build.ninja")}},
              "recorded_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
              "attestation": "Operator asserts this binary was successfully built from the recorded source."}
    write_json(out / "build.json", record)
    print(out / "build.json")


def prepare(args):
    spec, _ = configurations(args.config)
    corpus, out = args.corpus.resolve(), args.out.resolve()
    if out.is_relative_to(corpus):
        raise ValueError("study directory must be outside the corpus")
    if not corpus.is_dir():
        raise ValueError(f"corpus not found: {corpus}")
    root = Path(git(corpus, "rev-parse", "--show-toplevel").decode().strip())
    relroot = corpus.relative_to(root).as_posix()
    head = git(root, "rev-parse", "HEAD").decode().strip()
    if head != args.corpus_sha:
        raise ValueError(f"corpus HEAD {head} != explicitly pinned {args.corpus_sha}")
    # Ignore unrelated changes outside the corpus, but never accept untracked,
    # ignored, modified, or symlinked corpus files.
    if git(root, "status", "--porcelain", "--untracked-files=all", "--", relroot):
        raise ValueError("dirty corpus subtree")
    tracked = set(filter(None, git(root, "ls-files", "-z", "--", relroot).decode().split("\0")))
    files = sorted(corpus.rglob("*.smt2"), key=lambda p: p.relative_to(corpus).as_posix())
    if not files:
        raise ValueError("empty corpus")
    out.mkdir(parents=True, exist_ok=False)
    entries, rejected, seen, selected, duplicate_statuses = [], [], {}, [], defaultdict(set)
    fatal = []
    for path in files:
        rel = path.relative_to(corpus).as_posix()
        row = {"path": rel, "family": str(Path(rel).parent).replace("\\", "/")}
        try:
            if path.is_symlink() or not path.resolve().is_relative_to(corpus) or (
                    path.relative_to(root).as_posix() not in tracked):
                raise ValueError("untracked or symlinked corpus input")
            data = path.read_bytes()
            row["sha256"] = digest(data)
            info, prepared = inspect_problem(data)
            row.update(info)
            key = info["formula_sha256"]
            if row["expected"] in DECIDED:
                duplicate_statuses[key].add(row["expected"])
            if len(duplicate_statuses[key]) > 1:
                fatal.append({"path": rel, "error": "duplicate has contradictory :status",
                              "duplicate_of": seen[key]["path"]})
            if key in seen:
                original = seen[key]
                row["duplicate_of"] = original["path"]
                if (spec["schema"] == 1 and original["expected"] not in DECIDED
                        and row["expected"] in DECIDED):
                    original["expected"] = row["expected"]
                if spec["schema"] == 2:
                    selected.append((row, data, prepared))
            else:
                seen[key] = row
                selected.append((row, data, prepared))
            entries.append(row)
        except (ValueError, UnicodeError, RecursionError) as exc:
            row["rejection"] = str(exc)
            rejected.append(row)
    # Schema 1 keeps historical token deduplication. Schema 2 runs every file.
    if args.limit:
        n = min(args.limit, len(selected))
        selected = [selected[i * len(selected) // n] for i in range(n)]
    for index, (row, data, prepared) in enumerate(selected):
        row["id"] = f"{index:06d}"
        for dirname, contents in (("original", data), ("inputs", prepared)):
            path = out / dirname / (row["id"] + ".smt2")
            path.parent.mkdir(exist_ok=True)
            path.write_bytes(contents)
        row["input_sha256"] = digest(prepared)
    manifest = {"schema": 1, "corpus": str(corpus), "repository": str(root),
                "corpus_sha": head, "corpus_subtree": relroot,
                "corpus_tree": git(root, "rev-parse",
                                   "HEAD^{tree}" if relroot == "." else f"HEAD:{relroot}").decode().strip(),
                "selection": ("sorted POSIX paths; token dedup; evenly spaced floor(i*N/limit)"
                              if spec["schema"] == 1 else
                              "all sorted POSIX paths; no dedup; evenly spaced floor(i*N/limit)"),
                "limit": args.limit, "entries": entries, "rejected": rejected, "fatal": fatal,
                "selected": [row for row, _, _ in selected],
                "classification": "conservative syntactic certificates; aliases/quantifiers may be unclassified"}
    write_json(out / "manifest.json", manifest)
    write_json(out / "configurations.json", spec)
    print(f"prepared {len(selected)} / {len(files)}; rejected={len(rejected)}; "
          f"duplicates={sum('duplicate_of' in e for e in entries)}; {out / 'manifest.json'}")
    if fatal:
        raise ValueError("contradictory duplicate annotations; manifest is not runnable")


def parse_result(stdout, stderr, returncode, killed=False):
    text = stdout.decode(errors="replace")
    err = stderr.decode(errors="replace")
    verdicts = [line.strip() for line in text.splitlines() if line.strip() in DECIDED | {"unknown"}]
    reason = re.search(r'\(:reason-unknown\s+"([^"]*)"\)', text)
    reason = reason.group(1) if reason else ""
    combined = text + "\n" + err
    diagnostics = re.search(
        r"\(error\b|unknown parameter|invalid parameter|invalid model|error:|exception|segmentation fault",
        combined, re.IGNORECASE)
    # Errors override an apparent sat, including parameter/model errors.
    if diagnostics or len(verdicts) > 1:
        return "error", "diagnostic or multiple verdicts", verdicts
    if killed:
        return "timeout", "external wall deadline", verdicts
    if returncode != 0:
        return "error", f"exit {returncode}", verdicts
    if len(verdicts) == 1:
        result = verdicts[0]
        if result == "unknown" and ("timeout" in reason.lower() or "canceled" in reason.lower()):
            result = "timeout"
        return result, reason, verdicts
    if any(line.strip() == "timeout" for line in text.splitlines()):
        return "timeout", "solver process timer", verdicts
    return "error", "missing verdict", verdicts


def execute(argv, timeout, prefix, input_data=None):
    start = time.perf_counter()
    killed = False
    try:
        proc = subprocess.Popen(argv, stdin=subprocess.PIPE if input_data is not None else subprocess.DEVNULL,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            stdout, stderr = proc.communicate(input_data, timeout=max(0.001, timeout - (time.perf_counter() - start)))
        except subprocess.TimeoutExpired:
            killed = True
            proc.kill()  # exact child process only, never name-based termination
            stdout, stderr = proc.communicate()
        code = proc.returncode
    except OSError as exc:
        stdout, stderr, code = b"", str(exc).encode(), -1
    elapsed = time.perf_counter() - start
    prefix.parent.mkdir(parents=True, exist_ok=True)
    prefix.with_suffix(".stdout").write_bytes(stdout)
    prefix.with_suffix(".stderr").write_bytes(stderr)
    status, reason, verdicts = parse_result(stdout, stderr, code, killed)
    stats = {}
    for key, value in re.findall(rb":([A-Za-z0-9_.-]+)\s+(-?\d+(?:\.\d+)?)", stdout):
        stats[key.decode()] = float(value) if b"." in value else int(value)
    row = {"status": status, "reason": reason, "verdicts": verdicts, "returncode": code,
           "seconds": elapsed, "killed": killed, "argv": argv, "statistics": stats}
    if not killed and elapsed > timeout and status != "error":
        row.update(status="timeout", reason="completed after total wall deadline")
    write_json(prefix.with_suffix(".json"), row)
    return row


def summarize(rows, manifest, configs, baseline, timeout, expected_runs=None):
    counts = {c: dict.fromkeys(STATUSES, 0) for c in configs}
    strata = defaultdict(Counter)
    by_problem = defaultdict(dict)
    issues = []
    for row in rows:
        counts[row["config"]][row["status"]] += 1
        strata[(row["family"], row["category"], row["config"])][row["status"]] += 1
        by_problem[(row["id"], row["repeat"])][row["config"]] = row
        if row["status"] == "error":
            issues.append({"id": row["id"], "config": row["config"], "error": row["reason"]})
        if row["expected"] in DECIDED and any(
                v in DECIDED and v != row["expected"] for v in row["verdicts"]):
            issues.append({"id": row["id"], "config": row["config"], "error": "annotation contradiction"})
    # A disagreement across repetitions is a failure too, not just within pairs.
    observed = defaultdict(set)
    for row in rows:
        observed[row["id"]].update(v for v in row["verdicts"] if v in DECIDED)
    for ident, found in observed.items():
        if len(found) > 1:
            issues.append({"id": ident, "error": "contradictory solver verdicts"})
    pairs = {}
    for config in configs:
        if config == baseline:
            continue
        ratios, won, lost, par_base, par_other, n = [], 0, 0, 0.0, 0.0, 0
        for values in by_problem.values():
            if baseline not in values or config not in values:
                continue
            a, b = values[baseline], values[config]
            sa, sb = a["status"] in DECIDED, b["status"] in DECIDED
            if sa and sb and a["status"] == b["status"]:
                ratios.append(b["seconds"] / max(a["seconds"], 1e-9))
            won += sa and not sb
            lost += sb and not sa
            par_base += a["seconds"] if sa else 2 * timeout
            par_other += b["seconds"] if sb else 2 * timeout
            n += 1
        pairs[config] = {"paired_runs": n, "jointly_decided_same_verdict": len(ratios),
                         "geomean_other_over_baseline_joint_only": (
                             math.exp(sum(math.log(max(r, 1e-9)) for r in ratios) / len(ratios)) if ratios else None),
                         "baseline_only_decided": won, "other_only_decided": lost,
                         "par2_baseline_seconds": par_base, "par2_other_seconds": par_other}
    complete = expected_runs is None or len(rows) == expected_runs
    return {"counts": counts, "paired": pairs, "issues": issues,
            "completed_runs": len(rows), "expected_runs": expected_runs, "complete": complete,
            "valid_for_comparison": not issues and complete,
            "strata": [{"family": k[0], "category": k[1], "config": k[2], "counts": dict(v)}
                       for k, v in sorted(strata.items())],
            "timeout_treatment": "Joint-decision ratios exclude ALL undecided/error runs. "
                                 "PAR-2 charges 2*T for timeout, unknown, and error; "
                                 "any error/contradiction invalidates comparison. No invented solve times."}


def run(args):
    study = args.study.resolve()
    manifest = json.loads((study / "manifest.json").read_text())
    if manifest["fatal"]:
        raise ValueError("fatal corpus inconsistencies in manifest")
    if manifest["rejected"] and not args.accept_exclusions:
        raise ValueError("manifest has rejected inputs; inspect it and explicitly --accept-exclusions")
    if not manifest["selected"]:
        raise ValueError("no selected inputs")
    spec, configs = configurations(study / "configurations.json")
    if args.only:
        names = args.only.split(",")
        if any(n not in configs for n in names):
            raise ValueError("unknown configuration in --only")
        configs = {n: configs[n] for n in names}
    record = json.loads(args.build_record.read_text())
    source = args.source or Path(record["source"])
    build_dir = args.build_dir or Path(record["build_dir"])
    identity, _ = source_identity(source)
    if identity != record["source_identity"] or digest(args.z3.read_bytes()) != record["binary_sha256"]:
        raise ValueError("source or solver differs from build record; rebuild and record again")
    for n, expected in record["build_evidence"].items():
        if digest((build_dir / n).read_bytes()) != expected:
            raise ValueError("build configuration changed since attestation")
    for stream, expected in record.get("parameter_listing", {}).get("sha256", {}).items():
        if digest((args.build_record.parent / ("parameters." + stream)).read_bytes()) != expected:
            raise ValueError("parameter listing changed since build record")
    for entry in manifest["selected"]:
        for dirname, field in (("inputs", "input_sha256"), ("original", "sha256")):
            if digest((study / dirname / (entry["id"] + ".smt2")).read_bytes()) != entry[field]:
                raise ValueError("prepared/original input changed since manifest")
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    shutil.copytree(args.build_record.parent, out / "build-record")
    for name in ("manifest.json", "configurations.json"):
        shutil.copyfile(study / name, out / name)
    shutil.copytree(study / "inputs", out / "inputs")
    shutil.copytree(study / "original", out / "original")
    shutil.copyfile(Path(__file__), out / "runner.py")
    env = {"platform": platform.platform(), "machine": platform.machine(), "hostname": platform.node(),
           "processor": platform.processor(), "cpu_count": os.cpu_count(), "python": sys.version,
           "timeout_seconds": args.timeout, "memory_mb": args.memory_mb,
           "memory_policy": "Z3 -memory allocator limit (MB), not OS RSS; OOM is error",
           "jobs": 1, "repeats": args.repeats, "order": "rotate configurations by (input index + repetition)",
           "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    write_json(out / "environment.json", env)
    limits = [f"-t:{args.timeout * 1000}", f"-T:{args.timeout}", f"-memory:{args.memory_mb}", "-st"]
    solver = str(args.z3.resolve())
    # Exercise each complete argv, not just help/-p. Unknown nseq options can
    # otherwise be accepted until the SMT tactic is actually instantiated.
    for name, options in configs.items():
        row = execute([solver, *limits, *options, "-in"], args.timeout,
                      out / "preflight" / name,
                      b'(declare-const x String)(assert (str.in_re x (str.to_re "a")))\n'
                      b'(check-sat)\n(get-info :reason-unknown)\n')
        if row["status"] != "sat":
            write_json(out / "failure.json", {"error": "parameter/solver preflight failed", "config": name})
            raise ValueError(f"preflight failed for {name}; raw output retained")
    rows = []
    expected_runs = len(manifest["selected"]) * len(configs) * args.repeats
    with (out / "runs.jsonl").open("w", encoding="utf-8") as raw, (
            out / "runs.csv").open("w", newline="", encoding="utf-8") as csv_file:
        writer = csv.DictWriter(csv_file, fieldnames=RUN_FIELDS, extrasaction="ignore")
        writer.writeheader()
        for repeat in range(args.repeats):
            for i, entry in enumerate(manifest["selected"]):
                names = list(configs)
                rotation = (i + repeat) % len(names)
                names = names[rotation:] + names[:rotation]
                for name in names:
                    prefix = out / "raw" / entry["id"] / f"{repeat:03d}-{name}"
                    row = execute([solver, *limits, *configs[name],
                                   str(out / "inputs" / (entry["id"] + ".smt2"))],
                                  args.timeout, prefix)
                    row.update({k: entry[k] for k in ("id", "path", "family", "category", "expected")})
                    row.update(config=name, repeat=repeat)
                    rows.append(row)
                    raw.write(json.dumps(row, sort_keys=True) + "\n")
                    raw.flush()
                    writer.writerow(row)
                    csv_file.flush()
                    summary = summarize(rows, manifest, configs, spec["baseline"], args.timeout, expected_runs)
                    write_json(out / "summary.json", summary)
                    print(f"{entry['id']} {name}: {row['status']} {row['seconds']:.3f}s", flush=True)
    if source_identity(source)[0] != identity or digest(args.z3.read_bytes()) != record["binary_sha256"]:
        summary["valid_for_comparison"] = False
        summary["issues"].append({"error": "source or solver changed during measurements"})
        write_json(out / "summary.json", summary)
        write_json(out / "failure.json", {"error": "source or solver changed during measurements"})
        raise ValueError("source or solver changed during measurements")
    if summary["issues"]:
        raise ValueError("errors/contradictions retained in summary.json; results NOT valid for comparison")


def merge_results(args):
    """Aggregate disjoint configuration blocks without losing their provenance.

    Source directories must be retained: sources.json hashes their metadata and
    raw result streams, rather than pretending this summary is a raw archive.
    """
    roots = [p.resolve() for p in args.results]
    out = args.out.resolve()
    if len(set(roots)) != len(roots) or any(out.is_relative_to(p) for p in roots):
        raise ValueError("duplicate result directory or output inside a source result")
    rows, sources, inherited_issues = [], [], []
    reference, seen, arms = None, set(), set()
    policy_keys = ("platform", "machine", "hostname", "processor", "cpu_count",
                   "timeout_seconds", "memory_mb", "memory_policy", "jobs", "repeats")
    metadata_files = ("manifest.json", "configurations.json", "environment.json",
                      "build-record/build.json", "runs.jsonl", "summary.json")
    for root in roots:
        data = {name: (root / name).read_bytes() for name in metadata_files}
        manifest = json.loads(data["manifest.json"])
        spec, configs = configurations(root / "configurations.json")
        env = json.loads(data["environment.json"])
        record = json.loads(data["build-record/build.json"])
        previous = json.loads(data["summary.json"])
        local_rows = [json.loads(line) for line in data["runs.jsonl"].splitlines() if line.strip()]
        if not previous["complete"] or not local_rows:
            raise ValueError(f"incomplete or empty result block: {root}")
        if manifest["fatal"]:
            raise ValueError(f"fatal corpus inconsistencies: {root}")
        comparable = {
            "manifest": {k: v for k, v in manifest.items() if k not in ("corpus", "repository")},
            "configuration": spec,
            "source": record["source_identity"], "binary": record["binary_sha256"],
            "native_base_sha": record.get("native_base_sha"),
            "build_evidence": record["build_evidence"],
            "environment": {k: env[k] for k in policy_keys},
        }
        if reference is None:
            reference = comparable
            baseline = spec["baseline"]
            selected = {e["id"]: e for e in manifest["selected"]}
            timeout, repeats = env["timeout_seconds"], env["repeats"]
        elif comparable != reference:
            raise ValueError(f"mismatched corpus, configurations, build, hardware or limits: {root}")
        local_arms = {r["config"] for r in local_rows}
        if arms & local_arms or not local_arms <= configs.keys():
            raise ValueError(f"duplicate or unknown configuration block: {root}")
        expected = len(selected) * repeats * len(local_arms)
        if len(local_rows) != expected or previous["expected_runs"] != expected:
            raise ValueError(f"incorrect result count: {root}")
        for row in local_rows:
            key = (row["id"], row["repeat"], row["config"])
            if key in seen or row["id"] not in selected or not 0 <= row["repeat"] < repeats:
                raise ValueError(f"duplicate or unexpected measurement: {key}")
            entry = selected[row["id"]]
            if any(row[k] != entry[k] for k in ("path", "family", "category", "expected")):
                raise ValueError(f"measurement metadata differs from manifest: {key}")
            if row["status"] not in STATUSES or not math.isfinite(row["seconds"]) or row["seconds"] < 0:
                raise ValueError(f"invalid measurement status or time: {key}")
            seen.add(key)
            rows.append({**row, "source_result": str(root)})
        arms.update(local_arms)
        if not previous["valid_for_comparison"]:
            inherited_issues.append({"source": str(root), "error": "source summary invalidates comparison",
                                     "issues": previous["issues"]})
        sources.append({"directory": str(root), "configurations": sorted(local_arms),
                        "sha256": {name: digest(contents) for name, contents in data.items()}})
    if reference is None or arms != configs.keys():
        raise ValueError("merge requires every configuration in the frozen matrix")
    rows.sort(key=lambda r: (r["repeat"], r["id"], r["config"]))
    summary = summarize(rows, manifest, configs, baseline, timeout,
                        len(selected) * repeats * len(configs))
    summary["issues"].extend(inherited_issues)
    summary["valid_for_comparison"] = summary["complete"] and not summary["issues"]
    out.mkdir(parents=True, exist_ok=False)
    for name in ("manifest.json", "configurations.json"):
        shutil.copyfile(roots[0] / name, out / name)
    write_json(out / "sources.json", {
        "sources": sources, "comparison_identity": reference,
        "raw_data": "Retain all source result directories alongside this summary.",
        "order": "Configuration blocks; not the locally interleaved execution.",
    })
    with (out / "runs.jsonl").open("w", encoding="utf-8") as raw, (
            out / "runs.csv").open("w", newline="", encoding="utf-8") as csv_file:
        writer = csv.DictWriter(csv_file, fieldnames=RUN_FIELDS + ["source_result"], extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            raw.write(json.dumps(row, sort_keys=True) + "\n")
            writer.writerow(row)
    write_json(out / "summary.json", summary)
    print(f"merged {len(rows)} runs across {len(roots)} configuration blocks; {out / 'summary.json'}")
    if not summary["valid_for_comparison"]:
        raise ValueError("merged errors/contradictions retained; results NOT valid for comparison")


def positive(value):
    n = int(value)
    if n <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return n


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="command", required=True)
    p = sub.add_parser("prepare")
    p.add_argument("--corpus", type=Path, required=True)
    p.add_argument("--corpus-sha", required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--config", type=Path, default=CONFIG)
    p.add_argument("--limit", type=positive, help="omit for full manifest; never solves")
    p.set_defaults(action=prepare)
    p = sub.add_parser("record-build")
    p.add_argument("--source", type=Path, required=True)
    p.add_argument("--build-dir", type=Path, required=True)
    p.add_argument("--z3", type=Path, required=True)
    p.add_argument("--build-command", required=True)
    p.add_argument("--native-base-sha", help="pinned native ancestor of the instrumented source")
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--allow-dirty", action="store_true")
    p.set_defaults(action=record_build)
    p = sub.add_parser("run")
    p.add_argument("--study", type=Path, required=True)
    p.add_argument("--build-record", type=Path, required=True)
    p.add_argument("--z3", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--timeout", type=positive, default=10)
    p.add_argument("--memory-mb", type=positive, default=4096)
    p.add_argument("--repeats", type=positive, default=1)
    p.add_argument("--only", help="comma-separated configuration names; omit for the entire matrix")
    p.add_argument("--accept-exclusions", action="store_true")
    p.add_argument("--source", type=Path, help="relocated source; must match the build record")
    p.add_argument("--build-dir", type=Path, help="relocated build evidence; must match the build record")
    p.set_defaults(action=run)
    p = sub.add_parser("merge")
    p.add_argument("--results", type=Path, nargs="+", required=True)
    p.add_argument("--out", type=Path, required=True)
    p.set_defaults(action=merge_results)
    p = sub.add_parser("argv")
    p.add_argument("--config", type=Path, default=CONFIG)
    p.add_argument("--name", help="defaults to the frozen matrix's baseline")
    def print_argv(args):
        spec, configs = configurations(args.config)
        print(json.dumps(configs[args.name or spec["baseline"]]))
    p.set_defaults(action=print_argv)
    args = ap.parse_args(argv)
    try:
        args.action(args)
    except (ValueError, OSError, subprocess.SubprocessError, KeyError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
