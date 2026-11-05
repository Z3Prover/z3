#!/usr/bin/env python3
"""Translate the FMCAD 2025 SLEEC set benchmarks and compare native solvers.

Use --source for upstream's sleec/smtlib_set_quantifiers directory and --output
for an experiment directory. Without --z3/--cvc5, only prepare the inputs.
Both solver arguments enable timed runs, CSV results, raw logs, and Z3DB logging.
The default single worker avoids inter-solver CPU contention; larger values
measure concurrent throughput rather than isolated solver latency.
Manifest hashes cover UTF-8 input text with normalized LF newlines.

Tuples become single-constructor datatypes. all(p, S) becomes filter(p, S) = S;
some(p, S) becomes filter(p, S) != empty. Bounds over binary tuple products
become nested bounds, with tuple projections redirected to the two operands.
--universal-counterexamples instead encodes all(p, S) as filter(not p, S) = empty.
--simplify-finite-sets enables prototype bounded-filter preprocessing.
"""

import argparse
import collections
import concurrent.futures
import csv
import hashlib
import json
import platform
import re
import subprocess
import sys
import time
from pathlib import Path


def parse(text):
    tokens = re.findall(r';[^\n]*|"(?:[^"]|"")*"|\|[^|]*\||[()]|[^\s();]+', text)
    roots, stack = [], []
    for token in tokens:
        if token.startswith(";"):
            continue
        if token == "(":
            node = []
            (stack[-1] if stack else roots).append(node)
            stack.append(node)
        elif token == ")":
            if not stack:
                raise ValueError("unbalanced closing parenthesis")
            stack.pop()
        else:
            if not stack:
                raise ValueError("atom outside command")
            stack[-1].append(token)
    if stack:
        raise ValueError("unclosed parenthesis")
    return roots


def emit(node):
    return "(" + " ".join(map(emit, node)) + ")" if isinstance(node, list) else node


class Translator:
    def __init__(self, universal_counterexamples=False, simplify_finite_sets=False):
        self.tuples = {}
        self.constants = {}
        self.serial = 0
        self.universal_counterexamples = universal_counterexamples
        self.simplify_finite_sets = simplify_finite_sets
        self.simplification_stats = {}

    def tuple_name(self, fields):
        fields = tuple(fields)
        if not fields or any(f not in ("Int", "Bool") for f in fields):
            raise ValueError(f"unsupported tuple fields: {fields}")
        return self.tuples.setdefault(fields, f"__sleec_T{len(self.tuples)}")

    def selector(self, fields, index, value):
        if not 0 <= index < len(fields):
            raise ValueError("tuple selector out of range")
        return [f"{self.tuple_name(fields)}_{index}", value]

    def set_fields(self, node):
        if isinstance(node, str):
            return self.constants[node]
        if node[0] == "rel.product" and len(node) == 3:
            return self.set_fields(node[1]) + self.set_fields(node[2])
        raise ValueError(f"unsupported set expression: {emit(node)}")

    def bounded(self, op, predicate, domain, env):
        if predicate[0] != "lambda" or len(predicate[1]) != 1:
            raise ValueError("expected unary tuple lambda")
        name, sort = predicate[1][0]
        fields = self.set_fields(domain)
        if sort != ["Tuple", *fields]:
            raise ValueError("bounded variable and set sort mismatch")
        return self.bind(op, name, fields, predicate[2], domain, env)

    def bind(self, op, name, fields, body, domain, env):
        if isinstance(domain, list):
            if domain[0] != "rel.product" or len(domain) != 3:
                raise ValueError("expected binary relational product")
            left, right = domain[1:]
            if not isinstance(left, str) or not isinstance(right, str):
                raise ValueError("nested relational products are not supported")
            lf, rf = self.set_fields(left), self.set_fields(right)
            self.serial += 1
            ln, rn = f"__sleec_l{self.serial}", f"__sleec_r{self.serial}"
            replacement = {
                name: [self.selector(lf, i, ln) for i in range(len(lf))]
                + [self.selector(rf, i, rn) for i in range(len(rf))]
            }
            rewritten = self.replace_selectors(body, replacement)
            inner = [op, ["lambda", [[rn, ["Tuple", *rf]]], rewritten], right]
            return self.bind(op, ln, lf, inner, left, env)
        sort = self.tuple_name(fields)
        local = dict(env)
        local[name] = [self.selector(fields, i, name) for i in range(len(fields))]
        body = self.term(body, local)
        if op == "set.all" and self.universal_counterexamples:
            body = ["not", body]
        predicate = ["lambda", [[name, sort]], body]
        filtered = ["set.filter", predicate, domain]
        empty = ["as", "set.empty", ["FiniteSet", sort]]
        if op == "set.all":
            return ["=", filtered, empty if self.universal_counterexamples else domain]
        return ["not", ["=", filtered, empty]]

    def replace_selectors(self, node, replacements):
        if not isinstance(node, list):
            if node in replacements:
                raise ValueError("product tuple used without a selector")
            return node
        if (len(node) == 2 and isinstance(node[0], list)
                and node[0][:2] == ["_", "tuple.select"]
                and isinstance(node[1], str) and node[1] in replacements):
            return replacements[node[1]][int(node[0][2])]
        if node and node[0] == "lambda":
            local = {k: v for k, v in replacements.items()
                     if k not in {binding[0] for binding in node[1]}}
            return ["lambda", node[1], self.replace_selectors(node[2], local)]
        return [self.replace_selectors(child, replacements) for child in node]

    def term(self, node, env):
        if not isinstance(node, list):
            return node
        if node and isinstance(node[0], str) and node[0] in ("set.all", "set.some"):
            return self.bounded(node[0], node[1], node[2], env)
        if (len(node) == 2 and isinstance(node[0], list)
                and node[0][:2] == ["_", "tuple.select"]):
            return env[node[1]][int(node[0][2])]
        if node and node[0] in ("rel.product", "lambda", "Tuple", "Set"):
            raise ValueError(f"untranslated construct: {emit(node)}")
        return [self.term(child, env) for child in node]

    def translate(self, commands):
        output = []
        for cmd in commands:
            if cmd[0] in ("set-logic", "set-option", "get-model"):
                continue
            if cmd[0] == "declare-const":
                name, sort = cmd[1:]
                if sort[0] != "Set" or sort[1][0] != "Tuple":
                    raise ValueError(f"unsupported declaration: {emit(cmd)}")
                fields = tuple(sort[1][1:])
                self.constants[name] = fields
                output.append(["declare-const", name,
                               ["FiniteSet", self.tuple_name(fields)]])
            elif cmd[0] == "assert":
                output.append(["assert", self.term(cmd[1], {})])
            elif cmd == ["check-sat"]:
                output.extend([cmd, ["get-info", ":reason-unknown"]])
            else:
                raise ValueError(f"unsupported command: {emit(cmd)}")
        declarations = []
        for fields, name in self.tuples.items():
            constructor = [f"{name}_mk"] + [
                [f"{name}_{i}", field] for i, field in enumerate(fields)]
            declarations.append(["declare-datatypes", [[name, "0"]], [[constructor]]])
        commands = [
            ["set-logic", "ALL"], ["set-option", ":produce-models", "true"],
            *declarations, *output]
        if self.simplify_finite_sets:
            from finite_set_simplifier import FiniteSetSimplifier
            simplifier = FiniteSetSimplifier()
            commands = simplifier.simplify(commands)
            self.simplification_stats = dict(simplifier.stats)
        return "\n".join(map(emit, commands)) + "\n"


def prepare(source, output, universal_counterexamples=False, simplify_finite_sets=False):
    zdir, cdir = output / "z3", output / "cvc5"
    zdir.mkdir(parents=True, exist_ok=True)
    cdir.mkdir(parents=True, exist_ok=True)
    manifest = []
    for path in sorted(source.glob("*.smt2")):
        text = path.read_text(encoding="utf-8")
        if "__sleec_" in text:
            raise ValueError("reserved translator prefix occurs in input")
        commands = parse(text)
        if sum(cmd == ["check-sat"] for cmd in commands) != 1:
            raise ValueError(f"expected exactly one check-sat in {path}")
        translator = Translator(universal_counterexamples, simplify_finite_sets)
        start = time.perf_counter()
        translated = translator.translate(commands)
        translation_seconds = time.perf_counter() - start
        (zdir / path.name).write_text(translated, encoding="utf-8")
        # Retain the artifact's solver options, but exclude model printing.
        original = "\n".join(emit(cmd) for cmd in commands
                             if cmd[0] != "get-model") + "\n"
        (cdir / path.name).write_text(original, encoding="utf-8")
        manifest.append({
            "file": path.name,
            "source_sha256": hashlib.sha256(text.encode()).hexdigest(),
            "z3_sha256": hashlib.sha256(translated.encode()).hexdigest(),
        })
        if simplify_finite_sets:
            manifest[-1].update(simplifications=translator.simplification_stats,
                                translation_seconds=translation_seconds)
    if not manifest:
        raise ValueError(f"no SMT-LIB inputs in {source}")
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


def run_one(solver, binary, path, timeout, logdir, options=()):
    args = (["-smt2", "-st", f"-T:{timeout}", f"-t:{timeout * 1000}"] if solver == "z3"
            else [f"--tlimit={timeout * 1000}", "--stats"])
    command = [str(binary), *args, *options, str(path)]
    start = time.perf_counter()
    try:
        proc = subprocess.run(command, capture_output=True, timeout=timeout + 2)
        stdout, stderr, code = proc.stdout, proc.stderr, proc.returncode
    except subprocess.TimeoutExpired as exc:
        stdout, stderr, code = exc.stdout or b"", exc.stderr or b"", -1
    elapsed = time.perf_counter() - start
    out, err = stdout.decode(errors="replace"), stderr.decode(errors="replace")
    answers = re.findall(r"(?m)^(sat|unsat|unknown)\s*$", out)
    combined = out + "\n" + err
    if code == -1 or re.search(r"(?im)^timeout\s*$|interrupted by timeout", combined):
        result = "timeout"
    elif "(error " in out or code != 0:
        result = "error"
    elif len(answers) == 1:
        result = answers[0]
        if result == "unknown" and "timeout" in combined.lower():
            result = "timeout"
    else:
        result = "error"
    (logdir / f"{path.stem}.{solver}.stdout").write_bytes(stdout)
    (logdir / f"{path.stem}.{solver}.stderr").write_bytes(stderr)
    reason = re.search(r'\(:reason-unknown\s+"([^"]*)"', out)
    return {
        "file": path.name, "solver": solver, "result": result,
        "seconds": round(elapsed, 6), "exit_code": code,
        "reason": reason[1] if reason else "",
    }


def summarize(rows, timeout):
    summary = {}
    by_file = collections.defaultdict(dict)
    for row in rows:
        by_file[row["file"]][row["solver"]] = row
    for solver in ("z3", "cvc5"):
        selected = [r for r in rows if r["solver"] == solver]
        solved = [r for r in selected if r["result"] in ("sat", "unsat")]
        summary[solver] = {
            "counts": dict(collections.Counter(r["result"] for r in selected)),
            "solved_seconds": sum(r["seconds"] for r in solved),
            "wall_seconds": sum(r["seconds"] for r in selected),
            "par2_seconds": sum(r["seconds"] if r["result"] in ("sat", "unsat")
                                else 2 * timeout for r in selected),
        }
    common = [pair for pair in by_file.values() if len(pair) == 2
              and all(r["result"] in ("sat", "unsat") for r in pair.values())]
    summary["common_solved"] = len(common)
    summary["disagreements"] = [
        pair["z3"]["file"] for pair in common
        if pair["z3"]["result"] != pair["cvc5"]["result"]]
    summary["common_seconds"] = {
        s: sum(pair[s]["seconds"] for pair in common) for s in ("z3", "cvc5")}
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--z3", type=Path)
    parser.add_argument("--cvc5", type=Path)
    parser.add_argument("--timeout", type=int, default=20)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--z3-option", action="append", default=[],
                        help="additional Z3 key=value setting (repeatable)")
    parser.add_argument("--universal-counterexamples", action="store_true",
                        help="encode bounded all using empty counterexample filters")
    parser.add_argument("--simplify-finite-sets", action="store_true",
                        help="simplify fixed-point and unused bounded-filter predicates")
    args = parser.parse_args()
    manifest = prepare(args.source, args.output, args.universal_counterexamples,
                       args.simplify_finite_sets)
    print(f"Translated {len(manifest)} benchmarks.", flush=True)
    if not args.z3 and not args.cvc5:
        return
    if not args.z3 or not args.cvc5 or args.timeout < 1 or args.workers < 1:
        parser.error("provide both solvers and positive timeout/workers")
    binaries = {"z3": args.z3.resolve(), "cvc5": args.cvc5.resolve()}
    metadata = {
        "platform": platform.platform(), "processor": platform.processor(),
        "timeout_seconds": args.timeout, "workers": args.workers,
        "source": str(args.source.resolve()),
        "universal_counterexamples": args.universal_counterexamples,
        "simplify_finite_sets": args.simplify_finite_sets,
        "z3_options": args.z3_option,
        "versions": {s: subprocess.check_output(
            [str(b), "--version"], text=True).splitlines()[0]
            for s, b in binaries.items()},
    }
    (args.output / "run.json").write_text(json.dumps(metadata, indent=2) + "\n")
    logdir = args.output / "logs"
    logdir.mkdir(exist_ok=True)
    root = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(root / ".github" / "skills" / "shared"))
    from z3db import Z3DB, parse_stats
    db = Z3DB(str(root / ".z3-agent" / "z3agent.db"))
    rows = []
    fields = ["file", "solver", "result", "seconds", "exit_code", "reason"]
    with (args.output / "results.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        with concurrent.futures.ThreadPoolExecutor(args.workers) as pool:
            futures = {}
            for entry in manifest[:args.limit]:
                for solver, binary in binaries.items():
                    path = args.output / solver / entry["file"]
                    future = pool.submit(run_one, solver, binary, path,
                                         args.timeout, logdir,
                                         args.z3_option if solver == "z3" else ())
                    futures[future] = path
            for future in concurrent.futures.as_completed(futures):
                row = future.result()
                rows.append(row)
                writer.writerow(row)
                stream.flush()
                if row["solver"] == "z3":
                    text = futures[future].read_text()
                    run_id = db.start_run("benchmark", text)
                    stats = parse_stats((logdir / (
                        futures[future].stem + ".z3.stdout")).read_text())
                    db.log_formula(run_id, text, row["result"], stats=stats)
                    db.finish_run(run_id, row["result"],
                                  round(row["seconds"] * 1000), row["exit_code"])
                if len(rows) % 100 == 0:
                    print(f"{len(rows)} solver runs completed: "
                          f"{dict(collections.Counter(r['result'] for r in rows))}",
                          flush=True)
    db.close()
    summary = summarize(rows, args.timeout)
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
