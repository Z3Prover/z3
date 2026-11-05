import json, sys, collections, statistics

def analyze(path, label):
    recs = [json.loads(l) for l in open(path)]
    print(f"=== {label}: {len(recs)} files ===")
    print("keys:", list(recs[0].keys()))

    noproof_results = collections.Counter(r.get("z3_no_proof", {}).get("result") for r in recs)
    print("z3 (no proof) result counts:", dict(noproof_results))
    proof_results = collections.Counter(r.get("z3_with_proof", {}).get("result") for r in recs)
    print("z3 (with proof) result counts:", dict(proof_results))

    fcheck = collections.Counter(r.get("fstar_check", {}).get("status") if r.get("fstar_check") else "no_attempt" for r in recs)
    print("fstar_check status counts:", dict(fcheck))

    def times(key_path):
        vals = []
        for r in recs:
            d = r
            for k in key_path:
                d = d.get(k) if isinstance(d, dict) else None
                if d is None: break
            if isinstance(d, (int, float)):
                vals.append(d)
        return vals

    for name, kp in [("z3_no_proof.time", ["z3_no_proof","time"]),
                      ("z3_with_proof.time", ["z3_with_proof","time"]),
                      ("fstar_check.time", ["fstar_check","time"])]:
        vals = times(kp)
        if vals:
            print(f"{name}: n={len(vals)} mean={statistics.mean(vals):.3f} median={statistics.median(vals):.3f} max={max(vals):.3f} min={min(vals):.3f}")

    matched_total = sum(len(r.get("rewrite_matched", [])) for r in recs)
    unmatched_total = sum(len(r.get("rewrite_unmatched", [])) for r in recs)
    print("total matched leaves:", matched_total, "total unmatched leaves:", unmatched_total)

    matcher_hist = collections.Counter()
    for r in recs:
        for m in r.get("rewrite_matched", []):
            key = m if isinstance(m, str) else (m.get("pattern") if isinstance(m, dict) else str(m))
            matcher_hist[key]+=1
    print("matcher histogram:", dict(matcher_hist))

    unmatched_shapes = collections.Counter()
    for r in recs:
        for u in r.get("rewrite_unmatched", []):
            if isinstance(u, dict):
                shape = u.get("s","?")[:40]
            else:
                shape = str(u)[:40]
            unmatched_shapes[shape]+=1
    print("top unmatched shapes:")
    for k,v in unmatched_shapes.most_common(10):
        print(f"  {v:4d}  {k}")

    files_no_fstar = sum(1 for r in recs if not r.get("fstar_check"))
    print("files with no fstar attempt (no proof/parse fail):", files_no_fstar)
    print()

if __name__ == "__main__":
    analyze(sys.argv[1], sys.argv[2])
