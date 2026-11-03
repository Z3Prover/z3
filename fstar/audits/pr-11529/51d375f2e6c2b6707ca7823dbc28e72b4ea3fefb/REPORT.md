## Scope (partial)
PR #11529, head 51d375f2e6c2b6707ca7823dbc28e72b4ea3fefb, base 4629738b98b7b98d826833161cefbefdf1aeb928. PR open at that SHA; no prior audit comment.
Audited function: `bit2int::visit(app*)` mod branch, src/ast/rewriter/bit2int.cpp (new guard, head lines ~352-359, plus lowering below it).

## Obligations
1. **O1 (witness against BASE behavior, checked)**: for u=1, v=0 (bit-vectors) and a legal completion of integer mod at 0 with z(1)=2, `1 mod 0 = 2` while the lowering gives `bvurem 1 0 = 1`. Reachable in base because the branch only required `extract_bv(e2)` and !sign2. This is `base_witness`. It shows the fix is warranted; it is not a defect in the head.
2. **O2 (proved)**: under the head guard (e2bv is a BV numeral with k != 0), the emitted `(p + (d - (n urem d))) urem d` equals `(p - n) mod d` for every completion z of mod-at-0 (`lowering_exact`).
3. **O3 (proved)**: the intermediate sum after the one-bit zero_extend, p + (d - r) < 2^(w+1) when p,d < 2^w, so no wrap (`no_overflow`).

## Correspondence
F* `imod` models Int mod with an arbitrary total completion z at 0; `urem` models SMT-LIB bvurem (x urem 0 = x); `lowered` models the two-urem + sub + add + urem sequence for the pos1/neg1 case. The pos-only case (neg=0) is `lowered p 0 d = p % d`, a special instance. Width alignment (`align_sizes`) is modeled as value-preserving zero extension and is NOT mechanized.

## Assumptions / not verified
- Numerals unsigned, `!sign2` as in source; p, n, d naturals with width bound; alignment preserves values.
- Standard F* library lemmas only; no admits/assumes.
- Not checked: C++ execution, memory safety, mk_bv_* rewriter simplifications, cache/proof plumbing.

## Excluded changes
- `p = nullptr` reset in `bit2int::operator()` (proof ownership; manual review: looks correct, avoids stale proof reuse).
- src/ast/simplifiers/bit2int.h `pr ? mp(d.pr(), pr) : d.pr()` (proof plumbing; manual review OK).
- src/test/simplifier.cpp new tests (not audited; PR reports they pass).
- Other branches of bit2int::visit (eq/le/lt/ge/gt/mul/add) unchanged.
- Note: with a non-numeral or zero divisor the head keeps `mod` over original args (`m.mk_app(f,num_args,args)`), which is sound; the cost is lost optimization for symbolic divisors.

## Reproduce
```
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Bit2IntModAudit.fst
```