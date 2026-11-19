"""Export exact historical bytes; this preparation script does not stage or commit."""
import argparse
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


SOURCE = Path(__file__).resolve().parent
REPO = Path(r"C:\z3seq")
OUT = REPO / "doc" / "nfv-audits" / "c3mv-71ec455a1-batch6"
PREVIOUS = "4be813a75bdc59574df23da8ce5805a262171ba9"
POSITIVE_SEAL = "0c0a247024dc87b5dd8e896405973b2e945941ca4ac1e7e3a759e21382a3eda6"
FRESH = ["assemble_nfv6_publication.py", "validate_nfv6_publication.py", "replay_nfv6_checks.py", "test_nfv6_publication.py"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8", newline="\n")


def seal(root):
    paths = sorted(p for p in root.rglob("*") if p.is_file() and p != root / "manifest.json")
    exceptions = sorted(p.relative_to(root).as_posix() for p in paths if b"\r\n" in p.read_bytes())
    (root / ".gitattributes").write_text("* text eol=lf\n" + "".join(p + " -text\n" for p in exceptions), encoding="utf-8", newline="\n")
    notes = root / "export-notes.json"
    value = json.loads(notes.read_text())
    value["raw_crlf_exceptions"] = exceptions
    write_json(notes, value)
    write_json(root / "manifest.json", {"algorithm": "sha256", "self_excluded": "manifest.json", "files": [{"path": p.relative_to(root).as_posix(), "bytes": p.stat().st_size, "sha256": sha(p)} for p in sorted(root.rglob("*")) if p.is_file() and p != root / "manifest.json"]})


def assemble():
    def git(*args):
        return subprocess.check_output(["git", "--no-pager", *args], cwd=REPO, text=True).strip()
    assert not OUT.exists(), "Never overwrite an existing report directory"
    assert git("branch", "--show-current") == "c3mv" and git("rev-parse", "HEAD") == PREVIOUS
    assert not git("status", "--porcelain=v1", "-uall")
    assert git("rev-parse", "refs/stash") == "7af7fad70e9cea38601c67ff00d89f6b5576c2d6"
    assert git("rev-parse", "HEAD:src") == git("rev-parse", "71ec455a18702fe695d0c924a535ff9f385bd58d:src")
    assert sha(SOURCE / "nfv6-positive-initial-handoff.json") == POSITIVE_SEAL
    historical = {}

    def collect(name, expected=None):
        path = SOURCE.joinpath(*name.split("/"))
        assert path.resolve().is_relative_to(SOURCE)
        digest = sha(path)
        assert expected is None or digest == expected, name
        if name in historical:
            assert historical[name] == digest
            return
        historical[name] = digest
        if name.endswith("-handoff.json"):
            for child, value in json.loads(path.read_text())["files"].items():
                collect(child, value)

    for name in ["nfv6-baseline-handoff.json", "nfv6-coverage-handoff.json", "nfv6-selection-handoff.json", "nfv6-positive-initial-handoff.json"]:
        collect(name)
    for name in ["verify_nfv6.py", "test_nfv6_runner.py", "nfv6-checks/checks.json"]:
        collect(name)
    checks = json.loads((SOURCE / "nfv6-checks" / "checks.json").read_text())
    assert len(checks) == 4 and not (SOURCE / "nfv6-checks" / ".running").exists()
    assert sha(SOURCE / "nfv6-checks" / "checks.json") == sha(SOURCE / "nfv6-checks" / "stage-positive-initial" / "checks-prefix.json")
    for name in ["verify_nfv6.py", "test_nfv6_runner.py"]:
        assert sha(SOURCE / name) == sha(SOURCE / "nfv6-checks" / "stage-positive-initial" / name)
    for name in [*historical, *FRESH]:
        if name.endswith(".py"):
            ast.parse(SOURCE.joinpath(*name.split("/")).read_text(encoding="utf-8-sig"))
    OUT.mkdir(parents=True)
    for name, digest in historical.items():
        path = OUT.joinpath(*name.split("/"))
        path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(SOURCE.joinpath(*name.split("/")), path)
        assert sha(path) == digest
    for name in FRESH:
        (OUT / name).write_bytes((SOURCE / name).read_bytes().replace(b"\r\n", b"\n"))
    (OUT / "README.md").write_bytes((SOURCE / "nfv6-publication-readme.md").read_bytes().replace(b"\r\n", b"\n"))
    baseline = json.loads((OUT / "nfv6-baseline.json").read_text())
    names = ["c3mv-71ec455a1"] + ["c3mv-71ec455a1-batch" + str(n) for n in range(2, 6)]
    trees = git("rev-parse", *("HEAD:doc/nfv-audits/" + name for name in names)).splitlines()
    write_json(OUT / "publication-preflight.json", {"recorded_utc": datetime.now(timezone.utc).isoformat(), "branch": "c3mv", "previous_publication": PREVIOUS, "source": baseline["production_source"], "master": baseline["master"], "merge_base": baseline["merge_base"], "source_tree": baseline["source_tree"], "stash": baseline["stash"], "previous_report_trees": dict(zip(names, trees, strict=True)), "remote_poll_performed": False})
    write_json(OUT / "nfv6-results.json", {"kind": "manual local NFV-methodology audit; not hosted output", "source": baseline["production_source"], "master": baseline["master"], "merge_base": baseline["merge_base"], "property_id": "P23", "disposition": "audit failure: confirmed model/source correspondence mismatch", "summary": {"selected": 1, "verified": 0, "refuted": 0, "audit_failures": 1, "resources_exhausted": 0, "verifier_attempts": 4, "native_executions": 0, "new_verified_source_entries": 0, "admitted_model_domains": 16}, "source_correspondence_admitted": False, "checks_sha256": sha(OUT / "nfv6-checks" / "checks.json"), "positive_handoff_sha256": POSITIVE_SEAL, "isolated_repeat_cancelled": True, "new_verifier_invocations_for_report": 0, "followup": "After publication pre-freeze same-intent corrected retranslation, unchanged inputs/contracts/goals/all16examples, zero new source coverage and fresh validity/domain/whole-positive gates", "continuous_schedule_id": 2, "stop_schedule": False})
    write_json(OUT / "export-notes.json", {"policy": "Historical bytes preserved exactly, including CRLF; only new publication prose/tools normalized before hashing", "historical_files": historical, "fresh_tools": FRESH, "raw_crlf_exceptions": [], "no_historical_bytes_changed": True, "official_tool_binaries_vendored": False})
    seal(OUT)
    print(json.dumps({"status": "assembled; uncommitted", "historical_files": len(historical), "manifest_sha256": sha(OUT / "manifest.json"), "bundle": str(OUT)}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seal", type=Path, help="Reseal this uncommitted candidate after adding tool-validation logs")
    args = parser.parse_args()
    if args.seal is not None:
        assert args.seal.resolve() == OUT.resolve()
        assert not subprocess.check_output(["git", "ls-files", "--", str(OUT)], cwd=REPO)
        seal(OUT)
        print(json.dumps({"status": "candidate resealed", "manifest_sha256": sha(OUT / "manifest.json")}))
    else:
        assemble()
