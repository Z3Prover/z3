import hashlib
import json
from pathlib import Path

import verify_nfv6 as runner


ROOT = Path(__file__).resolve().parent


def main():
    model, prop = runner.load_sealed()
    pre_loop = [
        "used == 1",
        "size == |text|",
        "i == size",
        "text[..size] == text",
        "CountLowDigits(text[..i]) == CountLowDigits(text)",
    ]
    prefix = [
        "0 <= i < |text|",
        "|text[..i + 1]| == i + 1",
        "(text[..i + 1])[..i] == text[..i]",
        "(text[..i + 1])[i] == text[i]",
        "CountLowDigits(text[..i + 1]) == CountLowDigits((text[..i + 1])[..i]) + (if (text[..i + 1])[i] < 57 then 1 else 0)",
    ]
    text = model
    for anchor, clauses in [("  var i := size;\n", pre_loop), ("    i := i - 1;\n", prefix)]:
        assert text.count(anchor) == 1
        extra = "".join("// synth: explicit checked prefix/count proof annotation\n  assert " + c + ";\n" for c in clauses)
        text = text.replace(anchor, anchor + extra, 1)
    runner.checked_annotations(text, model)
    target = ROOT / "nfv6-proof-hints" / "001-prefix"
    assert not target.exists()
    target.mkdir(parents=True)
    path = target / "P23.dfy"
    path.write_text(text, encoding="utf-8", newline="\n")
    original_props = json.loads((ROOT / "nfv6-models" / "properties.json").read_text())
    original_props[0]["sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
    original_props[0]["proof_annotation_parent_sha256"] = prop["sha256"]
    (target / "properties.json").write_text(json.dumps(original_props, indent=2) + "\n", encoding="utf-8", newline="\n")
    receipt = {"status": "unproved annotation candidate", "parent_sha256": prop["sha256"], "candidate_sha256": original_props[0]["sha256"], "non_proof_computation_contract_hash": hashlib.sha256(runner.stable(text).encode()).hexdigest(), "added_assertions": pre_loop + prefix, "changed_computation": False, "changed_contracts_or_goals_or_examples": False, "verifier_attempts": 0}
    (target / "construction.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
