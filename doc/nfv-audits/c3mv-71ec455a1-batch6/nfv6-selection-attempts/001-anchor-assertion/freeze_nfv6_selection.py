import hashlib
import json
import pathlib
import subprocess
from datetime import datetime, timezone


ROOT = pathlib.Path(__file__).resolve().parent
REPO = pathlib.Path(r"C:\z3seq")
SOURCE = "71ec455a18702fe695d0c924a535ff9f385bd58d"
MASTER = "bcad05a7bf7dd9b82bd7a665018e0480e737264b"
BASE = "437536cd64a544a1c329fc57d83e56e294fdf47c"
PATH = "src/ast/simplifiers/seq_regular_simplifier.cpp"
MODULUS = 4294967296


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args):
    return subprocess.check_output(["git", "--no-pager", *args], cwd=REPO)


def save(name, value):
    path = ROOT / name
    assert not path.exists(), f"Refusing overwrite: {path}"
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8", newline="\n")
    return sha(path)


def main():
    inputs = {
        "nfv6-baseline-handoff.json": "4c93282be80f586d20857f97a8c3d978200a5a897d3e44b3d1c75a5aa765af7e",
        "nfv6-coverage-handoff.json": "a4510af4fef47c3ba7d68b3eaed784199e2adcf8857af269ff0010591d9aefe9",
    }
    for name, digest in inputs.items():
        assert sha(ROOT / name) == digest
        for child, child_digest in json.loads((ROOT / name).read_text())["files"].items():
            assert sha(ROOT / child) == child_digest
    assert git("branch", "--show-current").strip() == b"c3mv"
    assert git("rev-parse", "HEAD").strip() == b"4be813a75bdc59574df23da8ce5805a262171ba9"
    assert not git("status", "--porcelain=v1", "-uall")
    assert git("rev-parse", "refs/stash").strip() == b"7af7fad70e9cea38601c67ff00d89f6b5576c2d6"
    assert git("rev-parse", "HEAD:src") == git("rev-parse", SOURCE + ":src")
    assert git("rev-parse", "refs/remotes/origin/master").strip().decode() == MASTER
    blob = git("rev-parse", SOURCE + ":" + PATH).strip().decode()
    raw = git("cat-file", "blob", blob)
    assert hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest() == blob
    lines = raw.decode("utf-8").splitlines()
    assert REPO.joinpath(*PATH.split("/")).read_text(encoding="utf-8").splitlines() == lines
    spans = [[90, 97], [245, 266], [287, 315], [1492, 1503]]
    supplement = {
        "source": SOURCE,
        "path": PATH,
        "blob": blob,
        "sha256": hashlib.sha256(raw).hexdigest(),
        "spans": spans,
        "excerpts": [{"line": n, "text": lines[n - 1]} for lo, hi in spans for n in range(lo, hi + 1)],
        "purpose": "Selected whole entry, direct helper/tick behavior and empty/epsilon constructor values; no source execution",
    }
    assert "expr* decimal_greater" in lines[286] and lines[314].strip() == "}"
    assert "Shared suffixes" in lines[295]

    # This independent literal oracle generates examples, not native evidence or Dafny admission.
    def digits(n):
        return [ord(c) for c in str(n)]

    def capacity(n):
        ds = digits(n)
        return 0 if len(ds) > 4096 else 10 + 4 * len(ds) + 3 * sum(c < 57 for c in ds)

    def value(word):
        if not word or any(c < 48 or c > 57 for c in word):
            return -1
        result = 0
        for c in word:
            result = 10 * result + c - 48
        return result

    def expected(bound, word, inc_results, initial_steps, max_steps):
        if len(digits(bound)) > 4096:
            return {"language": [], "status": 1, "finalSteps": initial_steps, "used": 0}
        steps = initial_steps
        used = 0
        status = 0
        for ok in inc_results[:capacity(bound)]:
            used += 1
            if not ok:
                status = 2
                break
            steps = (steps + 1) % MODULUS
            if steps > max_steps:
                status = 1
                break
        size = len(word) + 1
        language = [] if status else [i <= j and value(word[i:j]) > bound for i in range(size) for j in range(size)]
        return {"language": language, "status": status, "finalSteps": steps, "used": used}

    cases = [
        ("empty-word", 0, [], 0, MODULUS - 1, None),
        ("all-zeros-equals-zero", 0, [48, 48], 0, MODULUS - 1, None),
        ("leading-zero-greater-zero", 0, [48, 49], 0, MODULUS - 1, None),
        ("higher-digit", 8, [57], 0, MODULUS - 1, None),
        ("nine-equality-no-higher-branch", 9, [57], 0, MODULUS - 1, None),
        ("nine-to-ten-length-transition", 9, [49, 48], 0, MODULUS - 1, None),
        ("leading-zeros-lexicographic", 10, [48, 48, 49, 49], 0, MODULUS - 1, None),
        ("multi-digit-equality", 10, [49, 48], 0, MODULUS - 1, None),
        ("invalid-letter", 10, [49, 97], 0, MODULUS - 1, None),
        ("overapproximated-symbol-domain", 0, [-7, 1114112], 0, MODULUS - 1, None),
        ("first-tick-canceled", 10, [49, 49], 0, MODULUS - 1, 0),
        ("last-tick-canceled", 10, [], 7, MODULUS - 1, -1),
        ("first-tick-over-budget", 9, [49, 48], 0, 0, None),
        ("wrapped-first-tick-then-over-budget", 9, [49, 48], MODULUS - 1, 0, None),
        ("unsigned-step-wrap-success", 9, [49, 48], MODULUS - 1, MODULUS - 1, None),
        ("ninety-nine-to-hundred", 99, [49, 48, 48], 0, MODULUS - 1, None),
    ]
    examples = []
    for name, bound, word, initial_steps, max_steps, canceled_at in cases:
        responses = [True] * capacity(bound)
        if canceled_at is not None:
            responses[canceled_at] = False
        examples.append({
            "id": name,
            "inputs": {"bound": bound, "word": word, "incResults": responses, "initialSteps": initial_steps, "maxSteps": max_steps},
            "expected": expected(bound, word, responses, initial_steps, max_steps),
            "domain_admission": "NOT YET CHECKED; independently prove all entry requires, then every-input pins, before positive/refutation acceptance",
        })
    assert capacity(0) == 17 and capacity(9) == 14 and capacity(10) == 24 and capacity(99) == 18
    assert examples[13]["expected"] == {"language": [], "status": 1, "finalSteps": 1, "used": 2}
    assert examples[14]["expected"]["finalSteps"] == 13
    requires = [
        ("bound >= 0", "Actual SASSERT integer/nonnegative applicability at entry; int input encodes the asserted integral rational"),
        ("0 <= initialSteps < 4294967296", "Representation of initial unsigned steps, not a no-overflow condition"),
        ("0 <= maxSteps < 4294967296", "Representation of unsigned max_steps; do not require initialSteps<=maxSteps"),
        ("|incResults| >= TickCapacity(bound)", "Finite observation-prefix encoding covers the largest direct-tick trace; unused tail may be arbitrary, including after an early exception"),
    ]
    helpers = [
        {"group": "Digits", "meaning": "Total canonical decimal rendering, for n>=0: n<10 yields [48+n], otherwise render(n/10)+[48+n%10]. Negative-input fallback [] is outside entry applicability. Do not accept caller-supplied rendered digits.", "source": [289, 300]},
        {"group": "Stoi", "meaning": "Total mathematical Horner decimal interpretation; empty or any symbol outside48..57 yields-1, arbitrary leading zeros accepted. Body, not external value/validity oracle.", "source": [293, 300, 306, 308, 312, 313, 314]},
        {"group": "TableAt / Empty / Epsilon / Literal / Range", "meaning": "For m=|word|, square (m+1)^2 table. Outside table/invalid i>j false. Empty allfalse,epsilon i==j,literal exact substring equality,range one-symbol substring in inclusive codepoint interval. Guard every index before access; bodies total.", "source": [245, 246, 247, 282, 283, 284, 1497, 1498]},
        {"group": "Cat / Union", "meaning": "Body-defined relational composition (exists split k with i<=k<=j and both memberships), and pointwise disjunction. Do not replace source construction with arithmetic comparison.", "source": [250, 251, 252, 253, 254, 255, 257]},
        {"group": "Star / finite-path helper", "meaning": "Body-defined zero-or-more relational closure: identity accepted, strictly advancing finite edges suffice for nonempty substrings; prove with decreasing substring length, no assumed equivalence oracle. Do not special-case decimal star as an unexplained parser predicate.", "source": [258, 309, 313]},
        {"group": "Tick / effectful Lit / effectful Cat / effectful Union / effectful Star / effectful Range", "meaning": "Each source tick consumes one incResults bit; false cancels BEFORE steps increment, true increments steps modulo2^32 and then tests >maxSteps. Stop at first failure and propagate exactly, without continuing later source computations. Keep/map pins have no arithmetic counter effects in this model.", "source": [90, 91, 92, 94, 245, 246, 250, 257, 258, 282, 283]},
        {"group": "TickCapacity / CountLowDigits", "meaning": "If |Digits(bound)|>4096 then0; else10+4*n+3*c, n=number of canonical digits, c=number below9. Derivation:1 initial range; each digit4 mandatory ticks plus3 for higher alternative;9 final ticks including THREE initializer-list concat calls. No arbitrary fuel or capped digit traversal.", "source": [251, 252, 253, 254, 255, 290, 292, 296, 297, 299, 300, 301, 302, 303, 304, 306, 308, 309, 310, 311, 312, 313, 314]},
        {"group": "ExpectedStatus / ExpectedSteps / ExpectedUsed", "meaning": "Independent specification of full expected callback/counter prefix, NOT language membership: oversized rendering gives budget with used0 and unchanged steps; else scan at most TickCapacity direct tick observations, cancel on first false, or increment modulo2^32 and budget-fail on first excess. If nonefail success. Every helper has a body; no requires assumes the desired output.", "source": [90, 91, 92, 290]},
    ]
    plan = {
        "stage": "nfv6-select", "status": "frozen selection only; no model or verifier invocation",
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "source": SOURCE, "master": MASTER, "merge_base": BASE,
        "nfv": "microsoft/neuro-formal-verification@599726579274cfeb1c0915414b911371527a9870",
        "selected_whole_properties": 1,
        "properties": [{
            "id": "P23", "candidate": "C14-nonnegative-decimal-language: complete underlying decimal_greater entry",
            "source_path": PATH, "source_span": [287, 315], "source_entry": "regular_compiler::decimal_greater",
            "grounding_quote": "Shared suffixes keep the lexicographic comparison linear in the numeral's size.",
            "hypothesis": "On every successfully completed construction, returned regex accepts exactly words whose SMT decimal conversion exceeds the asserted nonnegative integral bound. Preserve the entire constructor, conditional digit alternatives, leading zeros, final longer-number alternative, explicit4096-digit budget and all direct tick callback/counter outcomes.",
            "entry_name": "DecimalGreater",
            "inputs": [{"name": n, "type": t} for n, t in [("bound", "int"), ("word", "seq<int>"), ("incResults", "seq<bool>"), ("initialSteps", "int"), ("maxSteps", "int")]],
            "outputs": [{"name": n, "type": t} for n, t in [("language", "seq<bool>"), ("status", "int"), ("finalSteps", "int"), ("used", "int")]],
            "status_encoding": {"0": "completed", "1": "source explicit failure::budget", "2": "source explicit failure::canceled"},
            "requires": [{"text": text, "origin": "inferred", "optional": False, "justification": why} for text, why in requires],
            "ensures": [
                "status == ExpectedStatus(bound, incResults, initialSteps, maxSteps)",
                "finalSteps == ExpectedSteps(bound, incResults, initialSteps, maxSteps) && used == ExpectedUsed(bound, incResults, initialSteps, maxSteps)",
                "status != 0 ==> language == []",
                "status == 0 ==> |language| == (|word| + 1) * (|word| + 1)",
                "status == 0 ==> forall i: int, j: int :: 0 <= i <= |word| && 0 <= j <= |word| ==> language[i * (|word| + 1) + j] == (i <= j && Stoi(word[i..j]) > bound)",
            ],
            "whole_property_count": 1,
            "computation": [
                "Render bound with body-defined canonical Digits, then preserve size>4096 explicit failure before any direct tick.",
                "Build digits range0..9,suffix epsilon,greater empty.",
                "Traverse EVERY canonical digit right to left; tick, literal exact digit, concatenate exact+greater; if digit<9 construct higher range,cat higher+suffix,union; always cat digits+suffix.",
                "Construct nonzero range1..9,star digits,longer via EXACT three initializer-list cat calls,union; literal zero,star zero,and final concat zeros+greater.",
                "At every direct helper/loop tick preserve actual order,short-circuit on cancellation/budget,and expose used prefix and wrapped steps. On failure language=[] is only the transport sentinel for absent returned expression,not a source empty-regex result.",
            ],
            "planned_helpers": helpers,
            "helper_contract_policy": "No bodyless declarations,oracles,assumptions,verification attributes or decreases*. Use weakest total guards,not late helper-postcondition strengthening. Freeze actual helper signatures/contracts/bodies at MODEL seal before proof search; selection freezes the semantic obligations and input/goal/example meanings now.",
            "abstractions": [
                "Native regex AST expressions are represented by their body-defined membership tables on ALL substrings of an arbitrary queried word. This is not a native AST/rewriter equivalence proof; matrix helpers implement standard constructor denotations,not all seq_rewriter internals.",
                "Unbounded integer symbols overapproximate the native character alphabet; only48..57 are digits. No validity/value input oracle. Mathematical bigint rendering models asserted integral rational.to_string semantics,not the rational library internals.",
                "Unsigned counter model is32bits; increment wraps,including when initialSteps is UINT_MAX. No no-overflow premise. used is a mathematical trace index,not a new native counter.",
                "incResults encodes actual observed m.inc outcomes in order. A maximum-length prefix suffices for any behavior; unused suffix after failure has no meaning. No callback-growth or native concurrency claim.",
                "Only explicit regular_compiler tick failures and digit budget are transported. Allocation failure,AST identity/sharing/reference counts,pin lifetime,exceptions/resource work inside general constructors/rewriters and global-manager internals are not established. No native crash-freedom/termination or performance proof.",
                "No output-table numerical comparison may appear in entry computation or constructor helpers. Stoi comparison is specification/independent-example code only.",
            ],
            "examples": examples,
            "not_claimed": ["full decimal_language six-operator cache insertion/hit correctness", "nonnegative equality/inequality wrapper correctness", "new coverage of P9 negative-threshold branch", "native constructor/rewriter correspondence", "any confirmed C++ bug or crash"],
        }],
        "deferred": [
            {"scope": "C05", "reason": "No complete callback growth/reentrancy/backtracking frame or termination argument; do not assume native safety."},
            {"scope": "C13", "reason": "Paired producer control flow on normal return does not prove recursive substitution termination or native stack safety."},
            {"scope": "C14a", "reason": "Complete affine AST,DAG/cache and fallback semantics deserve a separate whole model; retain sentinel/saturating/depth-budget requirements. No safe arbitrary cached-bound premise."},
            {"scope": "C14b decimal_language wrapper", "reason": "Defer full six-operator/cache invariant wrapper,not its complete decimal_greater callee. P23 is ONE substantive changed function,not extra helper count padding. P9 remains historical negative-threshold-only coverage."},
        ],
        "preserved_open_intents": ["P13", "P18", "P20", "P21", "P22"],
        "acceptance_order": ["seal faithful model plus all helper/domain/goal metadata", "property-free validity by deleting ONLY entry ensures", "independent all-input concrete domain/caller admission for all16frozen examples", "complete original five-ensures positive as ONE property", "only then any independently admitted all-input pinned mechanical negation of the ENTIRE conjunction"],
        "domain_examples_note": "Literal expected outputs generated before modeling by a separate scalar Horner oracle and scalar resource simulation,not by table-constructor algorithm. These are not Dafny-proved admissions. No4096/4097-digit concrete-domain case is claimed; symbolic contract and actual branch must still cover the threshold without an extra size restriction.",
        "execution": {"verifier_invocations": 0, "native_executions": 0, "max_verifier_cores": 2, "future_wall_limit_seconds": 600},
        "next_stage": "nfv6-model", "schedule_id": 2, "stop_schedule": False,
    }
    hashes = dict(inputs)
    hashes["nfv6-selection-source-addendum.json"] = save("nfv6-selection-source-addendum.json", supplement)
    hashes["nfv6-selection.json"] = save("nfv6-selection.json", plan)
    hashes["nfv6-selection.md"] = sha(ROOT / "nfv6-selection.md")
    hashes["freeze_nfv6_selection.py"] = sha(pathlib.Path(__file__))
    hashes["nfv-methodology.md"] = sha(ROOT / "nfv-methodology.md")
    assert not git("status", "--porcelain=v1", "-uall")
    handoff = {"stage": "nfv6-select", "status": "done", "source": SOURCE, "master": MASTER, "merge_base": BASE, "files": hashes, "whole_properties": 1, "property_ids": ["P23"], "requires": 4, "optional_requires": 0, "ensures_counted_together": 5, "literal_examples": len(examples), "verifier_invocations": 0, "native_executions": 0, "next_stage": "nfv6-model", "schedule_id": 2, "stop_schedule": False}
    handoff_sha = save("nfv6-selection-handoff.json", handoff)
    print(json.dumps({"status": "frozen selection only", "properties": 1, "id": "P23", "inputs": 5, "outputs": 4, "requires": 4, "ensures_in_one_property": 5, "literal_examples": len(examples), "handoff_sha256": handoff_sha, "files": hashes}, indent=2))


if __name__ == "__main__":
    main()
