# F* audit of PR #11723 (head 0daaa82473156450c9f45e6a8a95ae8a1fae4893, base f46b3c58e41c0f9531cbb7cbab243b8cd2a98250)

Partial scope: 1 changed function group audited (`cross_nested::has_common_factor` / `split_with_var` budget checkpoints, src/math/lp/cross_nested.h). Source read from the PR patch (src/math/lp/cross_nested.h hunks around base lines 85-165 and 440-475) and base checkout.

## Obligations
1. **O1 (proved)**: the per-row divisibility scan with checkpoint(ch[i]->size()) returns true only if the unbudgeted scan returns true; returns false without the exhausted flag only if the original returns false.
2. **O2 (proved)**: same for the loop over common variables (`has_common_factor` after the PR, which returns false on exhaustion).
3. **O3 (proved)**: split_with_var proceeds (`!(has_common_factor(a) || m_limit_exceeded)`) only when the original would also see no common factor; hence budget exhaustion cannot produce a spurious cross-nested form via this path (it aborts, leaving m_limit_exceeded set).

## Correspondence / assumptions
`ck` models `checkpoint(cost)` (reslimit::inc(cost) as a budget test that sets m_limit_exceeded on failure; real reslimit also reports cancellation, modeled as exhaustion). Rows are lists of variable ids; `contains` is `mem`. The first-row variable list is a parameter. Uses only F* standard library; no admit/assume.

## Exclusions (not audited)
Other cross_nested.h changes (extract_common_factor, calc_occurences, pre_split abort returning false with a/b unset, explore_* checkpoints), horner.cpp, nla_grobner.cpp cancellation checks, nla_intervals.{h,cpp} (checkpoint throws default_exception; exception handling at callers not reviewed), tests. C++ execution, memory safety and exception safety are not mechanically verified. Note: reslimit costs are an accounting change; the PR does not alter the mathematical results except by aborting.

## Reproduce
See verification log.
