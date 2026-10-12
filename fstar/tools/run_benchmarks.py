#!/usr/bin/env python3
"""
Benchmark harness: for every .smt2 file in a given directory annotated
`:status unsat`, measure

  1. z3 without proof production,  10s timeout
  2. z3 with    proof production,  10s timeout
  3. F* (Pulse) proof checking of the extracted proof, 10s timeout

and classify every `Rewrite` leaf in the extracted proof via
`extract_z3_proof.classify_rewrite` (the Python mirror of
`Z3PatternMatchedProofChecker.fst`'s seven matchers), recording which
leaves matched a pre-verified lemma and which did not.

Results are appended as one JSON line per file to an output file, so a
run can be interrupted/resumed and inspected incrementally.
"""
import argparse
import json
import os
import subprocess
import sys
import time

import z3

FSTAR_TOOLS = r"C:\z3fstar\fstar\tools"
FSTAR_DIR = r"C:\z3fstar\fstar"
FSTAR_EXE = r"C:\fstar\fstar\bin\fstar.exe"
Z3_EXE = r"C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe"

sys.path.insert(0, FSTAR_TOOLS)
import extract_z3_proof as ezp  # noqa: E402


def is_unsat_annotated(path):
    try:
        with open(path, "r", errors="ignore") as f:
            for line in f:
                if ":status" in line and "unsat" in line:
                    return True
    except OSError:
        return False
    return False


def find_unsat_files(root):
    out = []
    for dirpath, _, filenames in os.walk(root):
        for fn in filenames:
            if fn.endswith(".smt2"):
                p = os.path.join(dirpath, fn)
                if is_unsat_annotated(p):
                    out.append(p)
    return sorted(out)


def run_phase(path, want_proof, timeout_ms):
    z3.set_param("proof", want_proof)
    ctx = z3.Context()
    s = z3.Solver(ctx=ctx)
    s.set("timeout", timeout_ms)
    try:
        s.add(z3.parse_smt2_file(path, ctx=ctx))
    except z3.Z3Exception as e:
        return {"result": "parse_error", "time": 0.0, "error": str(e)}
    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    out = {"result": str(r), "time": elapsed}
    if r == z3.unknown:
        out["reason_unknown"] = s.reason_unknown()
    if r == z3.unsat and want_proof:
        out["_solver"] = s
    return out


def check_fstar(fst_path, timeout_s):
    t0 = time.time()
    try:
        cp = subprocess.run(
            [FSTAR_EXE, "--include", FSTAR_DIR, "--smt", Z3_EXE, fst_path],
            cwd=FSTAR_DIR, capture_output=True, text=True, timeout=timeout_s,
        )
        elapsed = time.time() - t0
        passed = (cp.returncode == 0 and
                  "All verification conditions discharged successfully" in cp.stdout)
        return {
            "status": "pass" if passed else "fail",
            "time": elapsed,
            "returncode": cp.returncode,
            "stderr_tail": cp.stderr[-800:] if not passed else None,
        }
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "time": time.time() - t0}


def process_file(path, idx, total, timeout_s, fst_dir):
    rec = {"file": path, "idx": idx}
    print("[%d/%d] %s" % (idx, total, path), flush=True)

    r1 = run_phase(path, False, timeout_s * 1000)
    rec["z3_no_proof"] = {"result": r1["result"], "time": r1["time"],
                           "reason_unknown": r1.get("reason_unknown")}

    r2 = run_phase(path, True, timeout_s * 1000)
    rec["z3_with_proof"] = {"result": r2["result"], "time": r2["time"],
                             "reason_unknown": r2.get("reason_unknown")}

    if r2["result"] != "unsat" or "_solver" not in r2:
        rec["proof_extracted"] = False
        return rec

    s = r2["_solver"]
    try:
        pf = s.proof()
    except z3.Z3Exception as e:
        rec["proof_extracted"] = False
        rec["proof_error"] = str(e)
        return rec

    root = ezp.find_equational_root(pf)
    if root is None:
        rec["proof_extracted"] = False
        rec["proof_error"] = "no equational root found"
        return rec

    try:
        conv = ezp.Converter()
        root_ident = conv.proof(root)
    except Exception as e:
        rec["proof_extracted"] = False
        rec["proof_error"] = "conversion failed: %r" % (e,)
        return rec

    matched = [(ss.sexpr(), tt.sexpr(), name) for (ss, tt, name) in conv.rewrite_log if name is not None]
    unmatched = [(ss.sexpr(), tt.sexpr() if tt is not None else None)
                 for (ss, tt, name) in conv.rewrite_log if name is None]
    rec["proof_extracted"] = True
    rec["rewrite_leaves_total"] = len(conv.rewrite_log)
    rec["rewrite_matched"] = [{"s": ms, "t": mt, "pattern": mn} for (ms, mt, mn) in matched]
    rec["rewrite_unmatched"] = [{"s": us, "t": ut} for (us, ut) in unmatched]

    base = os.path.splitext(os.path.basename(path))[0]
    safe = "".join(c if c.isalnum() else "_" for c in base)[:60]
    module_name = "Bench_%d_%s" % (idx, safe)
    fst_path = os.path.abspath(os.path.join(fst_dir, module_name + ".fst"))
    try:
        src = ezp.generate(module_name, "benchmark file %s" % path, conv, root_ident, len(unmatched))
        with open(fst_path, "w") as f:
            f.write(src)
    except Exception as e:
        rec["proof_extracted"] = False
        rec["proof_error"] = "generate() failed: %r" % (e,)
        return rec

    rec["fstar_module"] = module_name
    fc = check_fstar(fst_path, timeout_s)
    rec["fstar_check"] = fc
    return rec


def _worker(args):
    path, idx, total, timeout_s, fst_dir = args
    try:
        return process_file(path, idx, total, timeout_s, fst_dir)
    except Exception as e:
        return {"file": path, "idx": idx, "fatal_error": repr(e)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("root", help="directory to scan for *.smt2 files")
    ap.add_argument("--out", required=True, help="output .jsonl file")
    ap.add_argument("--timeout", type=int, default=10, help="seconds")
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--fst-dir", default=None,
                     help="directory to write generated .fst files (default: alongside --out)")
    ap.add_argument("--skip", type=int, default=0, help="skip first N files (for resuming)")
    ap.add_argument("--workers", type=int, default=1,
                     help="number of parallel worker processes (each runs the full "
                          "z3-no-proof / z3-with-proof / fstar-check pipeline for one file)")
    args = ap.parse_args()

    fst_dir = os.path.abspath(args.fst_dir or (os.path.splitext(args.out)[0] + "_fst"))
    os.makedirs(fst_dir, exist_ok=True)

    files = find_unsat_files(args.root)
    if args.limit:
        files = files[args.skip:args.skip + args.limit]
    else:
        files = files[args.skip:]
    total = len(files)
    print("Found %d unsat-annotated files to process" % total, flush=True)

    mode = "a" if args.skip else "w"
    work_items = [(path, args.skip + i, total + args.skip, args.timeout, fst_dir)
                  for i, path in enumerate(files)]

    with open(args.out, mode) as outf:
        if args.workers > 1:
            import multiprocessing
            with multiprocessing.Pool(args.workers) as pool:
                done = 0
                for rec in pool.imap_unordered(_worker, work_items):
                    done += 1
                    outf.write(json.dumps(rec) + "\n")
                    outf.flush()
                    if done % 20 == 0 or done == total:
                        print("progress: %d/%d" % (done, total), flush=True)
        else:
            for item in work_items:
                rec = _worker(item)
                outf.write(json.dumps(rec) + "\n")
                outf.flush()

    print("Done. Wrote results to", args.out)



if __name__ == "__main__":
    main()
