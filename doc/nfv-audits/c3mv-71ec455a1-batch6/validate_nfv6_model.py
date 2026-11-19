import argparse
import ast
import hashlib
import json
import pathlib
import re
import subprocess


ROOT = pathlib.Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(models):
    handoff = ROOT / "nfv6-selection-handoff.json"
    assert sha(handoff) == "e0b67c6eb0ca54fc80f15ae00b2bd1633f2077d93f96227b5b37b507b5b48d01"
    for name, digest in json.loads(handoff.read_text())["files"].items():
        assert sha(ROOT / name) == digest, name
    prop = json.loads((ROOT / "nfv6-selection.json").read_text())["properties"][0]
    metadata, = json.loads((models / "properties.json").read_text())
    assert metadata["sha256"] == sha(models / "P23.dfy")
    assert metadata["selection_sha256"] == sha(ROOT / "nfv6-selection.json")
    assert metadata["inputs"] == prop["inputs"] and metadata["outputs"] == prop["outputs"]
    assert metadata["witnesses"] == prop["examples"] and len(metadata["witnesses"]) == 16
    raw = (models / "P23.dfy").read_text()
    code = re.sub(r"//[^\n]*", "", raw)
    declarations = list(re.finditer(r"^(function|method) (\w+)\(", code, re.M))
    blocks = {}
    for index, match in enumerate(declarations):
        block = code[match.start():declarations[index + 1].start() if index + 1 < len(declarations) else len(code)]
        header, body = block.split("\n{", 1)
        blocks[match[2]] = (header, body)
    entry_header, entry_body = blocks["DecimalGreater"]
    signature = "method DecimalGreater(" + ", ".join(i["name"] + ": " + i["type"] for i in prop["inputs"]) + ") returns (" + ", ".join(i["name"] + ": " + i["type"] for i in prop["outputs"]) + ")"
    assert entry_header.splitlines()[0] == signature
    clauses = lambda header, key: re.findall(r"^\s*" + key + r" (.+)$", header, re.M)
    assert clauses(entry_header, "requires") == [c["text"] for c in prop["requires"]]
    assert clauses(entry_header, "ensures") == prop["ensures"]
    helper_metadata = {h["name"]: h for h in metadata["environment"]}
    assert len(helper_metadata) == 29 and set(helper_metadata) == set(blocks) - {"DecimalGreater"}
    for name, helper in helper_metadata.items():
        header, body = blocks[name]
        assert body.strip().endswith("}") and helper["body_defined"]
        assert clauses(header, "requires") == [c["clause"] for c in helper["requires"]]
        assert clauses(header, "ensures") == helper["ensures"]
        assert all(c["origin"] == "inferred" and c["optional"] is False for c in helper["requires"])
    calls = {name: set(re.findall(r"\b(\w+)\s*\(", body)) & set(blocks) for name, (_, body) in blocks.items()}
    reachable = set()
    pending = ["DecimalGreater"]
    while pending:
        name = pending.pop()
        if name not in reachable:
            reachable.add(name)
            pending.extend(calls[name] - reachable)
    assert not reachable & {"Stoi", "ExpectedStatus", "ExpectedSteps", "ExpectedUsed", "Scan"}
    source = json.loads((ROOT / "nfv6-selection-source-addendum.json").read_text())
    source_lines = {r["line"]: r["text"].strip() for r in source["excerpts"]}
    entry_tagged = raw[raw.index("method DecimalGreater("):]
    entry_tags = {int(n) for n in re.findall(r"// src: [^:]+:(\d+) \|", entry_tagged)} | {287}
    significant = {n for n in range(287, 316) if source_lines[n] and source_lines[n] not in {"{", "}"} and not source_lines[n].startswith("//")}
    assert significant <= entry_tags, sorted(significant - entry_tags)
    assert len(re.findall(r"longer, status, finalSteps, used := MakeCat", entry_body)) == 3
    assert "if |text| > 4096 { status := 1; return; }" in entry_body
    assert "if digit < 9" in entry_body and "var digit := text[i] - 48;" in entry_body
    assert "if !inc[used] { status := 2; return; }" in blocks["Tick"][1]
    assert "stepsOut := (steps + 1) % 4294967296;" in blocks["Tick"][1]
    assert blocks["Tick"][1].index("if !inc[used]") < blocks["Tick"][1].index("stepsOut := (steps + 1)")
    assert "else if |inc| == 0 then [3, steps, 0]" in blocks["Scan"][1]
    assert len(re.findall(r"\bDigits\(bound\)", entry_body)) == 1
    ast.parse((ROOT / "build_nfv6_model.py").read_text())
    checked = subprocess.run(["python", "-B", str(ROOT / "check_nfv_provenance.py"), "--models", str(models)], capture_output=True, text=True, timeout=60)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    provenance = json.loads(checked.stdout)
    return {
        "status": "pass: construction/provenance checks ONLY",
        "whole_properties": 1,
        "entry": "DecimalGreater",
        "inputs": 5,
        "outputs": 4,
        "requires": 4,
        "ensures_counted_together": 5,
        "helpers_with_exact_contract_metadata": 29,
        "frozen_examples_unchanged": 16,
        "significant_selected_source_lines_tagged": len(significant),
        "no_result_or_resource_spec_oracle_reachable_from_computation": True,
        "explicit_direct_tick_order_wraparound_and_three_initializer_cats": "pass",
        "provenance": provenance,
        "model_sha256": metadata["sha256"],
        "not_claimed": "No property-free validity, concrete-domain, original-positive, refutation or native correctness check has run",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--models", type=pathlib.Path, required=True)
    args = parser.parse_args()
    print(json.dumps(validate(args.models), indent=2))
