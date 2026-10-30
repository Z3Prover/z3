# VerCors audit PR 11242 @ 3940b10cc7503ebbc64ea430f41bfc5cf8bdbd80 (base 5b25866d)
Verdict: inconclusive.

Selected function (only one): qsat::project in src/qe/qsat.cpp, head lines 936-1000 (loop 944-964). Source sha256 of decoded head file: fcd8717911e2ee53e746f54db740ee231281bb7bdf7e6e5f6ef5389ccd0d54fe.

Intended obligations: (1) projection_level stays in [1, m_level-1] and strictly decreases per iteration (no unsigned wraparound in `target + 1`, `m_level-1`); (2) UINT_MAX sentinel: `target + 1` cannot wrap since target==UINT_MAX is replaced by m_level%2; (3) loop exit leaves m_avars/fml consistent (needs callee contracts for m_mbp/compute_level; not provable without inventing contracts).

Outcome: all three inconclusive. Extract ProjLoop.cpp (callees abstracted as input arrays) was attempted with VerCors 2.4.0 C++ frontend: first run failed parsing '@' in a comment; second failed with 'Literal0Context ... not supported by VerCors' (unsigned literal 4294967295u). The frontend cannot faithfully express unsigned 32-bit semantics here; substituting mathematical ints would not correspond to the source, so I abstained. No passing unit, no counterexample claimed.

Excluded: scripts/*.py/.md/.json (not C++); src/test/* (test harness); qsat.cpp constructor/params/statistics changes (plumbing); compute_level trail push (obj_map/ref-counting object model unsupported).

Reproduce: /tmp/gh-aw/vercors/vercors --lang cpp --backend silicon --dev-total-timeout 60 (abs)/ProjLoop.cpp
Not a whole-PR theorem; failure to verify is not evidence of correctness.