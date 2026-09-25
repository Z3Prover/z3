# Regex equivalence study

This study branch is based on master commit
`6e585beeaebf9f7efd56b1105a72e5b5451796fc` plus the complete union-normalization
fix `81c61b39ae33e9f147e64d3590ba778b433e3d3d` (PR #10920).
The version string alone is insufficient to identify this baseline.

Build one Release binary with CMake and Ninja:

```sh
cmake -S . -B build -G Ninja -DCMAKE_BUILD_TYPE=Release
cmake --build build --target shell test-z3 --parallel 8
build/test-z3 /seq seq_regex_bisim seq_rewriter seq_regex_witness
```

`Z3_REGEX_STUDY_MODE=bisim` explicitly selects the normal bisimulation
algorithm; `Z3_REGEX_STUDY_MODE=subsumption` selects directional emptiness
of `p & ~q`, followed by `q & ~p` only if the first inclusion holds.
Unset means the original bisimulation path, without study diagnostics.
Other values are rejected when an equivalence check is invoked.
The controls affect regex equivalence checks, not the general SMT strategy.
They are study-only, not supported public Z3 parameters.

Both modes use the same derivative engine, normalizations, and existing
50,000-step equivalence budget. The two subsumption directions share this
budget; they must also share one external process deadline. Other internal
early exits and the SMT solver's handling of an undecided equivalence call
remain unchanged. The default benchmark wall deadline is five seconds.

With an explicit mode, stderr contains `regex-study ` followed by one JSON
start record and, if the call returns, one finish record. Multiple checks
may occur in one process. `expansions` counts main-loop derivative calls;
`cofactor_paths` counts enumerated paths, **not distinct successor leaves**.
`states` counts mapped regex nodes in bisimulation and visited residuals
across the two directional searches in subsumption. It is not a comparable
state-space cardinality across modes. An unfinished call has no final
counter record; it must not be interpreted as zero work.

The branch retains the earlier pilot's algorithms and counter locations,
but uses the new study environment name and diagnostic prefix. The old
`Z3_REGEX_PILOT_MODE` is not a control on this branch. Historical pilot
executables, patches, and measurements are separate immutable artifacts.
The machine-readable control contract is `scripts/regex_bisim_study.json`.
