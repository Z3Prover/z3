import argparse
import hashlib
import json
import pathlib
import re


ROOT = pathlib.Path(__file__).resolve().parent
SOURCE_PATH = "src/ast/simplifiers/seq_regular_simplifier.cpp"
MODULUS = "4294967296"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--draft", required=True)
    args = parser.parse_args()
    assert re.fullmatch(r"\d{3}", args.draft)
    handoff = ROOT / "nfv6-selection-handoff.json"
    assert sha(handoff) == "e0b67c6eb0ca54fc80f15ae00b2bd1633f2077d93f96227b5b37b507b5b48d01"
    for name, digest in json.loads(handoff.read_text())["files"].items():
        assert sha(ROOT / name) == digest, name
    selection = json.loads((ROOT / "nfv6-selection.json").read_text())
    prop = selection["properties"][0]
    addendum = json.loads((ROOT / "nfv6-selection-source-addendum.json").read_text())
    source = {r["line"]: r["text"].strip() for r in addendum["excerpts"]}
    target = ROOT / "nfv6-drafts" / args.draft
    assert not target.exists(), "Never overwrite a checked draft"
    target.mkdir(parents=True)
    rows = []
    helpers = []

    def emit(text, anchors=None):
        for line in text.splitlines():
            if not line.strip():
                continue
            if anchors is None:
                assert re.fullmatch(r"[{};]+|(?:requires|ensures|invariant|assert|decreases|reads|modifies)\b.*", line.strip()), line
                rows.append("// synth: checked contract, proof annotation, or structural delimiter")
            else:
                for n in anchors:
                    rows.append(f"// src: {SOURCE_PATH}:{n} | {source[n]}")
            rows.append(line)

    def helper(name, signature, body, anchors, requires=(), ensures=(), decreases=None, method=False):
        emit(("method " if method else "function ") + name + signature, anchors)
        for clause in requires:
            emit("  requires " + clause)
        for clause in ensures:
            emit("  ensures " + clause)
        if decreases:
            emit("  decreases " + decreases)
        emit("{")
        emit(body, anchors)
        emit("}")
        helpers.append({
            "name": name,
            "source": [{"path": SOURCE_PATH, "line": n, "text": source[n]} for n in anchors],
            "body_defined": True,
            "requires": [{"clause": c, "origin": "inferred", "optional": False, "reason": "Local index/unsigned representation condition established at every model call; not an assumed output property"} for c in requires],
            "ensures": list(ensures),
            "scope": "Focused denotational/explicit-resource model; native implementation correspondence and allocation/lifetime effects unproved",
        })

    helper("Digits", "(n: int): seq<int>",
           "  if n < 0 then [] else if n < 10 then [48 + n] else Digits(n / 10) + [48 + n % 10]",
           [288, 289], ensures=["n >= 0 ==> 0 < |Digits(n)|"], decreases="if n >= 0 then n else 0")
    helper("CountLowDigits", "(ds: seq<int>): int",
           "  if |ds| == 0 then 0 else CountLowDigits(ds[..|ds| - 1]) + (if ds[|ds| - 1] < 57 then 1 else 0)",
           [298, 301], ensures=["0 <= CountLowDigits(ds) <= |ds|"], decreases="|ds|")
    helper("TickCapacity", "(bound: int): int",
           "  if |Digits(bound)| > 4096 then 0 else 10 + 4 * |Digits(bound)| + 3 * CountLowDigits(Digits(bound))",
           [263, 264, 265, 266, 290, 292, 297, 299, 300, 301, 302, 303, 304, 306, 308, 309, 310, 311, 312, 313, 314],
           ensures=["0 <= TickCapacity(bound)"])
    helper("I", "(xs: seq<int>, k: int): int", "  if 0 <= k < |xs| then xs[k] else 0", [90, 91, 92])
    helper("B", "(xs: seq<bool>, k: int): bool", "  0 <= k < |xs| && xs[k]", [260, 262, 268, 269])
    helper("Scan", "(inc: seq<bool>, left: int, steps: int, limit: int): seq<int>",
           """  if left <= 0 then [0, steps, 0]
  else if |inc| == 0 then [3, steps, 0]
  else if !inc[0] then [2, steps, 1]
  else if (steps + 1) % 4294967296 > limit then [1, (steps + 1) % 4294967296, 1]
  else var rest := Scan(inc[1..], left - 1, (steps + 1) % 4294967296, limit);
       [I(rest, 0), I(rest, 1), 1 + I(rest, 2)]""",
           [90, 91, 92], ensures=["|Scan(inc, left, steps, limit)| == 3"], decreases="if left > 0 then left else 0")
    for name, index in [("ExpectedStatus", 0), ("ExpectedSteps", 1), ("ExpectedUsed", 2)]:
        oversized = ["1", "steps", "0"][index]
        helper(name, "(bound: int, inc: seq<bool>, steps: int, limit: int): int",
               f"  if |Digits(bound)| > 4096 then {oversized} else I(Scan(inc, TickCapacity(bound), steps, limit), {index})", [90, 91, 92, 290])
    helper("Stoi", "(word: seq<int>): int",
           """  if |word| == 0 then -1
  else if |word| == 1 then (if 48 <= word[0] <= 57 then word[0] - 48 else -1)
  else if 48 <= word[|word| - 1] <= 57 && Stoi(word[..|word| - 1]) >= 0
       then 10 * Stoi(word[..|word| - 1]) + word[|word| - 1] - 48
       else -1""", [292, 298, 308, 312, 314], decreases="|word|")
    helper("Width", "(word: seq<int>): int", "  |word| + 1", [260, 262, 268, 269], ensures=["Width(word) > 0"])
    helper("TableAt", "(table: seq<bool>, n: int, i: int, j: int): bool",
           "  n > 0 && 0 <= i <= j < n && 0 <= i * n + j < |table| && table[i * n + j]", [262, 268, 269])
    helper("Match", "(word: seq<int>, text: seq<int>, i: int, j: int): bool",
           "  0 <= i <= j <= |word| && word[i..j] == text", [257, 259, 260])
    helper("RangeAt", "(word: seq<int>, lo: int, hi: int, i: int, j: int): bool",
           "  0 <= i < |word| && j == i + 1 && lo <= word[i] <= hi", [283, 285])
    helper("CutAt", "(a: seq<bool>, b: seq<bool>, n: int, i: int, j: int): bool",
           "  n > 0 && 0 <= i <= j < n && exists k: int :: i <= k <= j && TableAt(a, n, i, k) && TableAt(b, n, k, j)", [262])
    helper("Reach", "(a: seq<bool>, n: int, i: int, j: int): bool",
           """  if n <= 0 || i < 0 || j < i || j >= n then false
  else if i == j then true
  else exists k: int :: i <= k < j && Reach(a, n, i, k) && TableAt(a, n, k, j)""", [269],
           decreases="if 0 <= i <= j then j - i else 0")
    tables = [
        ("MEmpty", "word: seq<int>", "false", [1497]),
        ("MEpsilon", "word: seq<int>", "k / Width(word) == k % Width(word)", [1498]),
        ("MLiteral", "text: seq<int>, word: seq<int>", "Match(word, text, k / Width(word), k % Width(word))", [257, 259, 260]),
        ("MRange", "lo: int, hi: int, word: seq<int>", "RangeAt(word, lo, hi, k / Width(word), k % Width(word))", [283, 285]),
        ("MCat", "a: seq<bool>, b: seq<bool>, word: seq<int>", "CutAt(a, b, Width(word), k / Width(word), k % Width(word))", [262]),
        ("MUnion", "a: seq<bool>, b: seq<bool>, word: seq<int>", "B(a, k) || B(b, k)", [268]),
        ("MStar", "a: seq<bool>, word: seq<int>", "Reach(a, Width(word), k / Width(word), k % Width(word))", [269]),
    ]
    for name, params, cell, anchors in tables:
        helper(name, "(" + params + "): seq<bool>", f"  seq(Width(word) * Width(word), k => {cell})", anchors,
               ensures=[f"|{name}({', '.join(p.strip().split(':')[0] for p in params.split(','))})| == Width(word) * Width(word)"])
    tick_requires = ["0 <= used < |inc|", "0 <= steps < 4294967296", "0 <= limit < 4294967296"]
    tick_ensures = [
        "usedOut == used + 1",
        "0 <= stepsOut < 4294967296",
        "status == (if !inc[used] then 2 else if (steps + 1) % 4294967296 > limit then 1 else 0)",
        "stepsOut == (if inc[used] then (steps + 1) % 4294967296 else steps)",
    ]
    helper("Tick", "(inc: seq<bool>, used: int, steps: int, limit: int) returns (status: int, stepsOut: int, usedOut: int)",
           """  usedOut := used + 1;
  stepsOut := steps;
  if !inc[used] { status := 2; return; }
  stepsOut := (steps + 1) % 4294967296;
  status := if stepsOut > limit then 1 else 0;""", [90, 91, 92], requires=tick_requires, ensures=tick_ensures, method=True)
    operations = [
        ("MakeRange", "lo: int, hi: int, ", "MRange(lo, hi, word)", [283, 284, 285]),
        ("MakeLiteral", "text: seq<int>, ", "MLiteral(text, word)", [257, 258, 259, 260]),
        ("MakeCat", "a: seq<bool>, b: seq<bool>, ", "MCat(a, b, word)", [262]),
        ("MakeUnion", "a: seq<bool>, b: seq<bool>, ", "MUnion(a, b, word)", [268]),
        ("MakeStar", "a: seq<bool>, ", "MStar(a, word)", [269]),
    ]
    for name, prefix, expression, anchors in operations:
        helper(name, "(" + prefix + "word: seq<int>, inc: seq<bool>, used: int, steps: int, limit: int) returns (language: seq<bool>, status: int, stepsOut: int, usedOut: int)",
               "  language := [];\n  status, stepsOut, usedOut := Tick(inc, used, steps, limit);\n  if status != 0 { return; }\n  language := " + expression + ";",
               anchors, requires=tick_requires,
               ensures=tick_ensures + ["status != 0 ==> language == []", "status == 0 ==> language == " + expression], method=True)

    params = ", ".join(i["name"] + ": " + i["type"] for i in prop["inputs"])
    returns = ", ".join(i["name"] + ": " + i["type"] for i in prop["outputs"])
    emit("method DecimalGreater(" + params + ") returns (" + returns + ")", [287])
    for r in prop["requires"]:
        emit("  requires " + r["text"])
    for e in prop["ensures"]:
        emit("  ensures " + e)
    emit("{")
    emit("  language := [];\n  status := 0;\n  finalSteps := initialSteps;\n  used := 0;", [287, 288, 90, 91, 92])
    emit("  var text := Digits(bound);", [289])
    emit("  if |text| > 4096 { status := 1; return; }", [290])
    emit("  var size := |text|;", [291])
    emit("  assert |incResults| >= 10 + 4 * size + 3 * CountLowDigits(text);")

    def call(result, method, arguments, anchors, declare=False):
        if declare:
            emit("  var " + result + ": seq<bool>;", anchors)
        emit("  " + result + ", status, finalSteps, used := " + method + "(" + arguments + ", word, incResults, used, finalSteps, maxSteps);", anchors)
        emit("  if status != 0 { return; }", anchors + [91, 92])

    call("digits", "MakeRange", "0, 9", [292], True)
    emit("  var suffix := MEpsilon(word);", [293])
    emit("  var greater := MEmpty(word);", [294])
    emit("  var i := size;\n  while i > 0", [295, 296])
    emit("    invariant 0 <= i <= size == |text|")
    emit("    invariant status == 0 && 0 <= finalSteps < 4294967296")
    emit("    invariant used == 1 + 4 * (size - i) + 3 * (CountLowDigits(text) - CountLowDigits(text[..i]))")
    emit("    invariant |incResults| >= 10 + 4 * size + 3 * CountLowDigits(text)")
    emit("    decreases i")
    emit("  {")
    emit("    i := i - 1;", [296])
    emit("    assert CountLowDigits(text[..i + 1]) == CountLowDigits(text[..i]) + (if text[i] < 57 then 1 else 0);")
    emit("    status, finalSteps, used := Tick(incResults, used, finalSteps, maxSteps);\n    if status != 0 { return; }", [297, 91, 92])
    emit("    var digit := text[i] - 48;", [298])
    call("exact", "MakeLiteral", "[text[i]]", [299], True)
    call("greater", "MakeCat", "exact, greater", [300])
    emit("    if digit < 9", [301])
    emit("    {")
    call("higher", "MakeRange", "digit + 1, 9", [302], True)
    call("alternative", "MakeCat", "higher, suffix", [303], True)
    call("greater", "MakeUnion", "greater, alternative", [304])
    emit("    }")
    call("suffix", "MakeCat", "digits, suffix", [306])
    emit("  }")
    call("nonzero", "MakeRange", "1, 9", [308], True)
    call("arbitrary", "MakeStar", "digits", [309], True)
    emit("  var longer := MEpsilon(word);", [263, 264, 310])
    for arg in ["nonzero", "suffix", "arbitrary"]:
        call("longer", "MakeCat", "longer, " + arg, [265, 310])
    call("greater", "MakeUnion", "greater, longer", [311])
    call("zeros", "MakeLiteral", "[48]", [312], True)
    call("zeros", "MakeStar", "zeros", [313])
    call("language", "MakeCat", "zeros, greater", [314])
    emit("}", [315])
    model = "\n".join(rows) + "\n"
    (target / "P23.dfy").write_text(model, encoding="utf-8", newline="\n")
    metadata = {
        "id": "P23", "path": SOURCE_PATH, "source_span": [287, 315], "entry_point": "DecimalGreater", "quote": prop["grounding_quote"],
        "sha256": sha(target / "P23.dfy"), "required_context": [SOURCE_PATH],
        "original_ensures": prop["ensures"],
        "assumptions": [{"clause": r["text"], **{k: v for k, v in r.items() if k != "text"}} for r in prop["requires"]],
        "environment": helpers, "witnesses": prop["examples"],
        "inputs": prop["inputs"], "outputs": prop["outputs"],
        "selection_sha256": sha(ROOT / "nfv6-selection.json"),
        "abstractions": prop["abstractions"] + [
            "Scan's status3 denotes exhausted finite observation data ONLY outside the admitted prefix-length contract; it is not a native cancellation result or an entry computation branch.",
            "I/B/TableAt/Match/RangeAt totalize invalid helper indices with0/false; every real entry/helper array access remains guarded. No missing callback is silently supplied.",
            "The unsigned postdecrement index is represented by its live descending mathematical index; final unused unsigned underflow on loop exit has no later observable read in this source entry.",
            "Source exceptions are lowered to status outputs and immediate return. language=[] on failure is absent-expression transport,not a native successful empty-language result.",
        ],
    }
    (target / "properties.json").write_text(json.dumps([metadata], indent=2) + "\n", encoding="utf-8", newline="\n")
    (target / "construction.json").write_text(json.dumps({"draft": args.draft, "builder_sha256": sha(pathlib.Path(__file__)), "model_sha256": metadata["sha256"], "helpers": len(helpers), "status": "unresolved draft; NOT verified", "verifier_invocations": 0}, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"draft": str(target), "helpers": len(helpers), "lines": len(rows), "model_sha256": metadata["sha256"], "properties": 1}, indent=2))


if __name__ == "__main__":
    main()
