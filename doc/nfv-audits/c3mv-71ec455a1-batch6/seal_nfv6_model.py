import ast
import hashlib
import json
import pathlib
import re
import shutil
import subprocess
from datetime import datetime, timezone


ROOT = pathlib.Path(__file__).resolve().parent
REPO = pathlib.Path(r"C:\z3seq")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def non_proof(path):
    code = re.sub(r"//[^\n]*", "", path.read_text())
    lines = [r.strip() for r in code.splitlines() if r.strip() and not re.match(r"\s*(assert|invariant|decreases)\b", r)]
    return hashlib.sha256(("\n".join(lines) + "\n").encode()).hexdigest()


def git(*args):
    return subprocess.check_output(["git", "--no-pager", *args], cwd=REPO)


def write(name, value):
    path = ROOT / name
    assert not path.exists(), name
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8", newline="\n")
    return sha(path)


def main():
    assert git("branch", "--show-current").strip() == b"c3mv"
    assert git("rev-parse", "HEAD").strip() == b"4be813a75bdc59574df23da8ce5805a262171ba9"
    assert not git("status", "--porcelain=v1", "-uall")
    assert git("rev-parse", "refs/stash").strip() == b"7af7fad70e9cea38601c67ff00d89f6b5576c2d6"
    assert git("rev-parse", "HEAD:src").strip() == b"caa5a9922f074f9f4adc8f7c98e1685be9626503"
    selection_handoff = ROOT / "nfv6-selection-handoff.json"
    assert sha(selection_handoff) == "e0b67c6eb0ca54fc80f15ae00b2bd1633f2077d93f96227b5b37b507b5b48d01"
    for name, digest in load(selection_handoff)["files"].items():
        assert sha(ROOT / name) == digest, name
    drafts = [ROOT / "nfv6-drafts" / n for n in ["001", "002"]]
    assert sha(drafts[0] / "P23.dfy") == "8efdcf8c8bfb7049144956b50ff95b12591e7737088a3e8e3c94954dd3635f59"
    assert sha(drafts[1] / "P23.dfy") == "e881b914e70e17a7887c6b8d991755cdec6e54e178ad313e9a8565f817a2bcbe"
    assert non_proof(drafts[0] / "P23.dfy") == non_proof(drafts[1] / "P23.dfy")
    for draft in drafts:
        result = load(draft / "resolve.json")
        assert result["exit_code"] == 0 and result["solver_invocations"] == 0
        assert result["model_sha256"] == sha(draft / "P23.dfy")
        assert result["raw_log_sha256"] == sha(draft / "resolve.log")
        assert b"did not attempt verification" in (draft / "resolve.log").read_bytes()
        validation = load(draft / "construction-validation.json")
        assert validation["status"].startswith("pass") and validation["model_sha256"] == result["model_sha256"]
        assert validation["significant_selected_source_lines_tagged"] == 25
        metadata, = load(draft / "properties.json")
        assert len(metadata["environment"]) == 29
        assert sum(len(h["requires"]) for h in metadata["environment"]) == 18
        assert sum(len(h["ensures"]) for h in metadata["environment"]) == 46
    current_builder = ROOT / "build_nfv6_model.py"
    final_builder = drafts[1] / current_builder.name
    assert not final_builder.exists()
    shutil.copyfile(current_builder, final_builder)
    for draft in drafts:
        assert sha(draft / current_builder.name) == load(draft / "construction.json")["builder_sha256"]
    for name in ["build_nfv6_model.py", "validate_nfv6_model.py", "seal_nfv6_model.py", "check_nfv_provenance.py"]:
        ast.parse((ROOT / name).read_text(encoding="utf-8-sig"))
    canonical = ROOT / "nfv6-models"
    assert not canonical.exists()
    canonical.mkdir()
    for name in ["P23.dfy", "properties.json"]:
        shutil.copyfile(drafts[1] / name, canonical / name)
        assert (drafts[1] / name).read_bytes() == (canonical / name).read_bytes()
    files = {
        name: sha(ROOT / name)
        for name in ["build_nfv6_model.py", "validate_nfv6_model.py", "seal_nfv6_model.py", "check_nfv_provenance.py", "nfv6-selection-handoff.json", "nfv6-selection-validation.json", "nfv6-model.md", "nfv6-models/P23.dfy", "nfv6-models/properties.json"]
    }
    for draft in drafts:
        for path in sorted(draft.iterdir()):
            assert path.is_file(), path
            files[path.relative_to(ROOT).as_posix()] = sha(path)
    freeze = {
        "stage": "nfv6-model", "status": "sealed before proof search; resolution and provenance ONLY",
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "source": "71ec455a18702fe695d0c924a535ff9f385bd58d",
        "master": "bcad05a7bf7dd9b82bd7a665018e0480e737264b",
        "merge_base": "437536cd64a544a1c329fc57d83e56e294fdf47c",
        "files": files,
        "model_sha256": sha(canonical / "P23.dfy"),
        "non_proof_computation_contract_hash": non_proof(canonical / "P23.dfy"),
        "selected_properties": 1, "property_ids": ["P23"], "inputs": 5, "outputs": 4,
        "requires": 4, "optional_requires": 0, "ensures_as_one_property": 5,
        "helpers": 29, "local_helper_requires": 18, "checked_helper_postcondition_obligations": 46,
        "helper_postconditions_note": "46 declared helper postconditions are NOT yet proven; all must pass the property-free validity gate",
        "literal_examples": 16, "source_tags": 377, "significant_selected_lines": 25,
        "syntax_resolution_attempts": 2, "syntax_resolution_passes": 2,
        "verification_attempts": 0, "solver_invocations": 0, "native_executions": 0,
        "allowed_future_changes": "Sound verified asserts/invariants/decreases only; unchanged computation, entry/helper signatures/contracts, all goals, domains and examples",
        "toolchain": {"dafny": "4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2", "solver": "bundled z3-4.12.1.exe", "cores_total": 2, "per_obligation_seconds": 30, "whole_file_watchdog_seconds": 600},
        "next_stage": "nfv6-verify", "schedule_id": 2, "stop_schedule": False,
    }
    freeze_sha = write("nfv6-model-freeze.json", freeze)
    report = (ROOT / "nfv6-model.md").read_text()
    for link in re.findall(r"\]\(([^)]+)\)", report):
        assert (ROOT / link).is_file(), link
    assert not git("status", "--porcelain=v1", "-uall")
    handoff = {"stage": "nfv6-model", "status": "done", "files": {"nfv6-model-freeze.json": freeze_sha, **files}, "model_sha256": freeze["model_sha256"], "property_ids": ["P23"], "syntax_resolution_only": True, "verification_attempts": 0, "native_executions": 0, "next_stage": "nfv6-verify", "schedule_id": 2, "stop_schedule": False}
    handoff_sha = write("nfv6-model-handoff.json", handoff)
    print(json.dumps({"status": freeze["status"], "properties": 1, "helpers": 29, "resolution_passes": 2, "model_sha256": freeze["model_sha256"], "non_proof_hash": freeze["non_proof_computation_contract_hash"], "freeze_sha256": freeze_sha, "handoff_sha256": handoff_sha, "source_stash_five_publications_and_worktree": "unchanged", "next_stage": "nfv6-verify"}, indent=2))


if __name__ == "__main__":
    main()
