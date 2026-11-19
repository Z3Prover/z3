"""Offline validation of preserved evidence; success does NOT admit correspondence."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True

import verify_nfv6 as runner


PIN = "71ec455a18702fe695d0c924a535ff9f385bd58d"
MASTER = "bcad05a7bf7dd9b82bd7a665018e0480e737264b"
BASE = "437536cd64a544a1c329fc57d83e56e294fdf47c"
POSITIVE_SEAL = "0c0a247024dc87b5dd8e896405973b2e945941ca4ac1e7e3a759e21382a3eda6"


def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def at(root, name):
    path = root.joinpath(*name.split("/")).resolve()
    assert path.is_relative_to(root.resolve()) and path.is_file() and not path.is_symlink(), name
    return path


def check_history(root, history, model, prop):
    checks = root / "nfv6-checks"
    candidate_path = root / "nfv6-proof-hints" / "001-prefix" / "P23.dfy"
    candidate = runner.checked_annotations(candidate_path.read_text(), model)
    assert [r["sequence"] for r in history] == [1, 2, 3, 4]
    assert [r["kind"] for r in history] == ["validity", "validity", "domain", "proof"]
    for row in history:
        text = at(checks, row["input"]).read_text()
        log = at(checks, row["log"]).read_text(encoding="utf-8-sig")
        for key, digest in [("input", "input_sha256"), ("log", "raw_log_sha256"), ("runner", "runner_sha256")]:
            assert runner.sha(at(checks, row[key])) == row[digest]
        summary = re.search(r"Dafny program verifier finished with (\d+) verified, (\d+) errors?", log)
        assert summary is not None
        assert (int(summary[1]), int(summary[2])) == (row["internal_obligations_verified"], row["diagnostic_errors"])
        admitted = row["exit_code"] == 0 and not row["wall_timed_out"] and int(summary[1]) > 0 and int(summary[2]) == 0
        assert row["admitted"] == admitted, "Recorded admission contradicts actual exit/raw diagnostics"
        assert not row["wall_timed_out"] and row["wall_seconds"] == 600
        assert not re.search(r"timed out|time outs?", log, re.I)
        command = row["command"]
        assert command[command.index("--solver-path") + 1].endswith("z3-4.12.1.exe")
        assert command[command.index("--cores") + 1] == "2"
        assert command[command.index("--verification-time-limit") + 1] == "30"
        assert not row["mbqi_override"] and not row["isolate_assertions"]
        assert not any(c.startswith("--filter") or c in ["--isolate-assertions", "--dont-verify-dependencies", "--solver-option"] for c in command)
        assert row["retained_entry_requires"] == [a["clause"] for a in prop["assumptions"]]
        assert row["retained_helpers"] == 29 and row["canonical_sha256"] == prop["sha256"]
        full = model if row["sequence"] == 1 else candidate
        assert row.get("full_goal_candidate_sha256", row["canonical_sha256"]) == (prop["sha256"] if row["sequence"] == 1 else runner.sha(candidate_path))
        if row["kind"] == "validity":
            assert text == runner.validity_only(full, prop)
        elif row["kind"] == "domain":
            assert row["domain_example_ids"] == [e["id"] for e in prop["witnesses"]], "Incomplete domain group"
            assert row["gate_validity_sequence"] == runner.prior_validity(history[:row["sequence"] - 1], prop["sha256"], runner.sha(candidate_path))["sequence"]
            assert text == runner.domain_callers(runner.validity_only(candidate, prop), prop)
        else:
            assert row["gate_validity_sequence"] == 2 and row["gate_domain_sequence"] == 3
            runner.prior_domains(history[:3], prop["sha256"], runner.sha(candidate_path), [e["id"] for e in prop["witnesses"]], 2)
            assert text == runner.original_positive(candidate, prop)
            assert at(checks, row["input"]).read_bytes() == candidate_path.read_bytes()
            assert row["checked_original_ensures"] == prop["original_ensures"]
        assert row["removed_ensures"] == ([] if row["kind"] == "proof" else prop["original_ensures"])
        assert not row.get("whole_property_refuted", False) and not row.get("whole_property_verified", False)
        assert load(checks / (Path(row["input"]).stem + ".result.json")) == row
        start = load(checks / (Path(row["input"]).stem + ".start.json"))
        assert all(row[k] == v for k, v in start.items() if k != "runner_sha256")
        assert start["runner_sha256"] == row["runner_sha256"]
    assert [r["exit_code"] for r in history] == [4, 0, 0, 4]
    for stage, length in [("stage-initial", 1), ("stage-prefix", 2), ("stage-domain", 3), ("stage-positive-initial", 4)]:
        assert load(checks / stage / "checks-prefix.json") == history[:length]


def source_inventory(root):
    inventory = load(root / "nfv6-coverage-source-inventory.json")
    addendum = load(root / "nfv6-selection-source-addendum.json")
    assert inventory["head"] == addendum["source"] == PIN
    files = {f["path"]: f for f in inventory["files"]}
    assert addendum["blob"] == files[addendum["path"]]["blob"]
    assert addendum["sha256"] == files[addendum["path"]]["sha256"]
    excerpts = {}
    for item in inventory["files"] + [addendum]:
        for line in item["excerpts"]:
            key = item["path"], line["line"]
            assert key not in excerpts or excerpts[key] == line["text"]
            excerpts[key] = line["text"]
    return files, excerpts


def check_sources(repo, files, excerpts):
    def git(*args):
        return subprocess.check_output(["git", "--no-pager", *args], cwd=repo)
    assert git("merge-base", PIN, MASTER).decode().strip() == BASE
    tree = {}
    for line in git("ls-tree", "-r", PIN, "--", *sorted(files)).decode().splitlines():
        descriptor, name = line.split("\t")
        tree[name] = descriptor.split()[2]
    assert tree == {name: item["blob"] for name, item in files.items()}
    objects = list(dict.fromkeys(f["blob"] for f in files.values()))
    raw = subprocess.run(["git", "cat-file", "--batch"], cwd=repo, input=("\n".join(objects) + "\n").encode(), capture_output=True, check=True).stdout
    offset, blobs = 0, {}
    for wanted in objects:
        end = raw.index(b"\n", offset)
        identity, kind, size = raw[offset:end].split()
        assert identity.decode() == wanted and kind == b"blob"
        start, length = end + 1, int(size)
        data = raw[start:start + length]
        assert len(data) == length and raw[start + length:start + length + 1] == b"\n"
        assert hashlib.sha1(b"blob " + str(length).encode() + b"\0" + data).hexdigest() == wanted
        blobs[wanted] = data
        offset = start + length + 1
    assert offset == len(raw)
    for name, item in files.items():
        data = blobs[item["blob"]]
        assert hashlib.sha256(data).hexdigest() == item["sha256"]
        lines = data.decode("utf-8").splitlines()
        for (path, number), text in excerpts.items():
            if path == name:
                assert lines[number - 1] == text


def validate(root, repo=None):
    root = root.resolve()
    manifest = load(root / "manifest.json")
    listed = set()
    for row in manifest["files"]:
        path = at(root, row["path"])
        assert path not in listed and path.stat().st_size == row["bytes"] and runner.sha(path) == row["sha256"], row["path"]
        listed.add(path)
    assert listed == {p for p in root.rglob("*") if p.is_file() and p != root / "manifest.json"}
    exceptions = sorted(p.relative_to(root).as_posix() for p in listed if b"\r\n" in p.read_bytes())
    assert load(root / "export-notes.json")["raw_crlf_exceptions"] == exceptions
    assert (root / ".gitattributes").read_text() == "* text eol=lf\n" + "".join(p + " -text\n" for p in exceptions)
    assert runner.sha(root / "nfv6-positive-initial-handoff.json") == POSITIVE_SEAL
    for handoff in root.glob("nfv6-*-handoff.json"):
        for name, digest in load(handoff)["files"].items():
            assert runner.sha(at(root, name)) == digest, name
    model, prop = runner.load_sealed(root)
    history = load(root / "nfv6-checks" / "checks.json")
    check_history(root, history, model, prop)
    assert len(prop["inputs"]) == 5 and len(prop["outputs"]) == 4
    assert len(prop["assumptions"]) == 4 and len(prop["original_ensures"]) == 5 and len(prop["witnesses"]) == 16
    names = re.findall(r"^(?:function|method) (\w+)\(", model, re.M)
    assert set(names) - {prop["entry_point"]} == {e["name"] for e in prop["environment"]}
    assert len(names) == 30 and all(e["body_defined"] for e in prop["environment"])
    files, excerpts = source_inventory(root)
    tags = re.findall(r"^// src: (.+?):(\d+) \| (.*)$", model, re.M)
    assert len(tags) == 377
    for path, number, text in tags:
        assert excerpts[path, int(number)].strip() == text
    finding = load(root / "nfv6-correspondence-failure.json")
    assert finding["source_line"] == 285 and finding["source_pin"] == PIN
    assert excerpts[finding["source_file"], 285] == finding["source_text"]
    assert "'0' + lo, '0' + hi" in finding["source_text"]
    assert model.splitlines()[271].strip() == "0 <= i < |word| && j == i + 1 && lo <= word[i] <= hi"
    assert "RangeAt(word, lo, hi," in model.splitlines()[339]
    assert not finding["source_correctness_admitted"] and not finding["sealed_model_changed"]
    for contrast in finding["arithmetic_contrasts"]:
        lo, hi, code = [contrast[k] for k in ["lo", "hi", "character_code"]]
        assert contrast["frozen_helper_predicate"] == (lo <= code <= hi)
        assert contrast["source_declared_ascii_predicate"] == (48 + lo <= code <= 48 + hi)
        assert contrast["frozen_helper_predicate"] != contrast["source_declared_ascii_predicate"]
    results = load(root / "nfv6-results.json")
    assert results["summary"] == {"selected": 1, "verified": 0, "refuted": 0, "audit_failures": 1, "resources_exhausted": 0, "verifier_attempts": 4, "native_executions": 0, "new_verified_source_entries": 0, "admitted_model_domains": 16}
    assert results["source"] == PIN and results["master"] == MASTER and results["merge_base"] == BASE
    assert results["checks_sha256"] == runner.sha(root / "nfv6-checks" / "checks.json")
    assert results["positive_handoff_sha256"] == POSITIVE_SEAL
    assert not results["source_correspondence_admitted"] and results["isolated_repeat_cancelled"]
    for path in root.rglob("*.py"):
        ast.parse(path.read_text(encoding="utf-8-sig"), filename=str(path))
    for path in root.rglob("*.md"):
        prose = re.sub(r"```.*?```", "", path.read_text(), flags=re.S)
        for link in re.findall(r"\]\(([^)]+)\)", prose):
            if not link.startswith(("https://", "http://", "#")):
                target = (path.parent / link.split("#")[0]).resolve()
                assert target.is_relative_to(root) and target.is_file(), (str(path), link)
    if repo is not None:
        check_sources(repo, files, excerpts)
    return {"status": "pass", "files": len(listed) + 1, "historical_verifier_attempts": 4, "new_verifier_invocations": 0, "source_files": len(files), "source_tags": len(tags), "pinned_git_sources_checked": repo is not None, "whole_verified": 0, "whole_refuted": 0, "model_audit_failures": 1, "source_correspondence_admitted": False, "native_executions": 0}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--repo", type=Path)
    args = parser.parse_args()
    print(json.dumps(validate(args.bundle, args.repo), indent=2))
