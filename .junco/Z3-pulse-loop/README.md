# Local Pulse proof-checker loop

Each `wf.yml` execution handles one item from the F* proof-checker regression queue. `Regress` measures the private branch tip. `Analytics` sends the same case and diagnostics to a read-only Leader (Astra/high) and the sole Developer (Opus/high). Developer also receives the finished plan. `Verify` builds the captured patch separately. `Record` returns the local verdict, evidence, patch and commit to the frontend. An empty queue runs neither model.

## Run

Requires Linux, a writable Btrfs mount with `user_subvol_rm_allowed`, Bun, a built Junco checkout and frontend client, `pwsh`, CMake/C++/GMP, Python, the pinned F* release, and the `aeneas` OCaml 5.3.0 switch with `ocamlfind` and `zarith`. `bun run link` uses `$JUNCO` or `$HOME/git/junco`. Grafana must already serve its Junco Prometheus datasource on port 8000. The workflow never owns that service.

```sh
cd .junco/Z3-pulse-loop
bun run link
bun run check                    # private local fixtures, no paid requests or service state
bun run wf.ts --prepare           # build/diagnose/select only; item ID on stdout
bun run wf.ts --once --allow-paid # at most one graph; no idle or crash retry
bun run loop --allow-paid         # continuous; intentional stops/configuration errors do not restart
```

Use `--prepare` and `--once` directly, not through the supervisor. `$source` sends the previous iteration to `Regress`. After recording, `Record -> Regress` carries the verdict back; only a verdict matching that iteration and branch tip reaches `$sink`. In continuous mode its iteration seeds the next graph with fresh agent sessions. `--once` stops at that sink. The frontend, recorder and state lock stay open across cycles. The service pauses ten minutes on idle/unbuildable tips and backs off sixty seconds after runtime failures. A paid flag is never implicit.

- `Z3_PULSE_LOOP_REPO`: read-only local Z3 checkout (default `~/git/z3`). First use fetches its local `origin/master` SHA, or the immutable `Z3_PULSE_LOOP_BASE`, into a separate private repository. Later cycles start at `loop/pulse-local`.
- `Z3_PULSE_LOOP_STATE`: new private state, default `/btrfs/Z3-pulse-loop-local`. Use an owned, real directory with mode 0700. No remotes, reset, clean or migration of previous state. A second owner or unexpected dirty tree is an error: inspect the evidence, not `git reset --hard`.
- `Z3_PULSE_LOOP_CORPUS`: clean pinned z3test checkout (default `/btrfs/Z3-pulse-loop/z3test`). Campaign: `91c60596fd6a43de189a1ccba8080a3b48797537`, all 17 `regressions/proofs` and 225 hash-manifest-selected `regressions/smtlib-sample` cases, `Z3_PULSE_LOOP_MAX_CASES=0`.
- `FSTAR_EXE`: `/opt/fstar-v2026.09.27/bin/fstar.exe`; `OPAMSWITCH=aeneas`.
- `Z3_PULSE_LOOP_MODEL_STORE`: private nonsecret Copilot catalog populated by the installed Pi updater with the saved login. The workflow loads this catalog offline. It checks both contexts, prices and supported thinking before creating agents. OMP's `-1m` suffix is not a Pi model ID. Model-free preparation needs no catalog or login.
- `GRAFANA_URL`: `http://localhost:8000` by default. Startup prints the dashboard URL with its stream selector. The Junco Monitor is at `http://127.0.0.1:3000/`, listening on **all interfaces**. Missing assets, a port collision, or a mismatched Grafana datasource fails startup.

**Trust boundary:** the worker uses ordinary Btrfs and the operator's Unix UID, not an OS sandbox. The native shell receives a minimal environment, separate home/build scratch and a per-process 1,800 CPU-second limit. Absolute paths and host sockets accessible to that UID remain accessible. Do not run untrusted work under an account whose privileges you would not give the worker. The frontend has no authentication and displays raw messages and tool I/O; use a trusted network. No role is assigned credentials, Docker operations or publication. Cgroup pipeline memory is reported only with actual delegation.

## What counts

The host runs `fstar/tools/build_ocaml_checker.ps1 -RunTests` with checkout Z3, the native uninstrumented checker and a pinned external regression harness. Native bridge tests are not the separate in-memory Pulse tests. `ACCEPT` alone certifies a formula. A complete pre-existing failed case can become a work item; missing inputs, failed infrastructure, incomplete diagnostics or an altered evaluator are not improvements. Stats totals are from checker stderr and reported with their case coverage.

Queue order is least attempts, then crash, reject, obligation family, timeout and slow case, then weight. The judge requires no new soundness marker or disallowed per-case regression, plus a targeted or corpus improvement. Previously near-budget cases use the existing 80% noise rule; targeted speedups use the existing 20% threshold.

Inspect `queue.json`, `analytics.jsonl` and `runs/<iteration>/result.json` under the private state. Changed attempts include `attempt.patch` (full indexed binary diff, including new files). An accepted patch advances only the private branch; rejection retains evidence and reverses only the still-identical patch. The frontend shows the same result. `accept` counts formulas, `accepted_change` counts retained changes, and `queue_open` counts remaining work. No issues, PRs, remote branches, or external merges are created.
