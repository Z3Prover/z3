# Batch 3 source stage: P12 pattern-length and first-case applicability

## Result and boundaries

Bounded source tracing found **no explicit pattern-length rejection excluding
2,147,483,647 characters in the inspected constructors/callers**. The chosen
length fits the last non-wrapping capacity growth of the default zstring buffer
on a 64-bit size_t target. This does NOT prove successful allocation or native
solver reachability, and does NOT upgrade the batch-2 scalar model refutation
to a confirmed native bug, crash, or wrong SAT/UNSAT result.

A source consequence is now clearer: IF an active obligation with that literal
length reaches the selected split plugin, its initial case is exactly one, the
wrapped guard returns false, and an unconditional VERIFY failure path is taken.
VERIFY is not debug-only in this source. The configured action exits or throws
an exception, not an unchecked return with an uninitialized edge. No such path
was executed. No new Dafny property was selected, implemented, or checked here.

Source remains pinned at `71ec455a18702fe695d0c924a535ff9f385bd58d`, with master
`d738f81eab9af1468394664a812fe4310ae8e1fa`, merge base
`437536cd64a544a1c329fc57d83e56e294fdf47c`. Local HEAD is audit-only publication
`146f70d7ddf5507fdf731af2511edf4c5f669fc5`; its src tree equals the pinned head.
No remote poll, checkout, pull/rebase, native build/run, huge literal allocation,
production edit, or stash action was performed in this stage.

## Literal representation and constructors

- `src\util\zstring.h:30-75`: storage is `buffer<uint32_t>`, the sized constructor
  appends an unsigned number of supplied characters, and `length()` returns its
  unsigned size. `well_formed()` checks character values, not total string length
  (`src\util\zstring.cpp:96-106`). Repeated ASCII 97 is within the character
  domain; that observation is not a construction/allocation test.
- `src\api\api_seq.cpp:48-91`: null-terminated, length-delimited byte, and sized
  UTF-32 constructors all form zstrings and pass them to `str.mk_string`. The
  byte constructor checks null-buffer validity then copies unsigned `sz` items;
  the UTF-32 route directly passes the caller's unsigned size/valid array to the
  zstring constructor. No total-length cap below the witness appears in these
  bodies. The public declarations use unsigned lengths, not signed lengths
  (`src\api\z3_api.h:3928-3945`). Valid caller buffers remain a prerequisite.
- `src\ast\ast.h:125-147` stores a zstring parameter through an allocated zstring,
  not an integer/string-length field. `src\ast\seq_decl_plugin.cpp:714-720`
  constructs a single-parameter string-constant declaration; the corresponding
  declaration validation checks kind/arity, not a length cap (502-508).
  Literal extraction copies the stored zstring (920-932), with no truncation
  to a smaller explicit length domain in that body. Copies add resource cost.
- SMT2 scanner `read_string` accumulates a dynamic string buffer until the end
  quote (`src\parsers\smt2\smt2scanner.cpp:194-216`, scanner.h:40-56), and the
  expression parser builds a zstring/string AST (smt2parser.cpp:1268-1275).
  These particular bodies contain no explicit token-length cap. This is NOT a
  proof that every parser counter, vector, front end or caller supports such a
  giant token; the direct sized C API route avoids relying on the text route.

## Buffer growth is not itself an exclusion proof for this witness

`src\util\buffer.h:26-77,137-166,193-211` has unsigned position/capacity, initial
capacity 16, expansion by `m_capacity << 1`, element append through push_back,
and allocation using `sizeof(T) * new_capacity`. For the witness, the last
required growth is 2^30 -> 2^31, still representable as unsigned 32-bit capacity.
The requested length 2^31-1 is below that capacity. The NEXT doubling would wrap
to zero, but is not required merely to hold this witness. Therefore citing
pre-existing capacity doubling as automatically excluding P12 is unjustified.

On the 64-bit size_t interpretation, 2^31 four-byte code units require an
8-GiB final backing buffer, excluding old capacity, client arrays, intermediate
copies, ASTs and allocator overhead. This arithmetic explains the large resource
premise; no memory was allocated to test it. A 32-bit address-space target and
configured or physical memory limits may prevent construction much earlier.

`src\util\memory_manager.cpp:70-81,120-130,268-290,312-333,389-414` distinguishes
configured global limits from malloc failure and allocation exceptions. A zero
global maximum is the no-explicit-global-limit value used by the inspected
checks; zero does not promise available memory. No fixed source-level string
length bound below 2^31-1 follows from those allocation bodies. This is bounded
inspection, not proof of the absence of all limits throughout Z3 or its clients.

## Term normalization, registration and actual case-number source

`seq_rewriter::mk_seq_replace_all` (`src\ast\rewriter\seq_rewriter.cpp:2295-2341`)
handles empty/equal operands and fully evaluable literals/units, otherwise returns
BR_FAILED. A selected distinct opaque input is not forced through its literal
evaluation path; `try_get_unit_values` also rejects that opaque input before the
short-circuited attempt on the pattern (2573-2588). This does not account for all
other rewrites, earlier equalities, substitutions or successful evaluations.

`src\smt\theory_nseq.cpp:592-613` registers replace_all when the pattern is a
nonempty literal; no upper bound is checked in that branch. Input/result/
replacement are tokenized, not the pattern itself. A replacement length axiom
can be added. `replace_all_facet::add` stores the literal unchanged
(`src\ast\seq\seq_replace_all_facet.h:30-70`), and its apply_subst only changes
result/input/replacement, not the literal pattern (cpp:24-41). Propagation can
discharge/split known input prefixes first (cpp:132-210). These are genuine
remaining applicability conditions, not assumed away.

`replace_all_split::split` visits active obligations and directly calls
`VERIFY(apply_case(n, idx, 1, out))` before marking commitment (cpp:271-283).
Thus the witness case number one is the actual initial caller value, not an
arbitrary out-of-range model input. The iterator begins at one and increments
for later cases (header:103-110; cpp:286-288). The admission guard precedes both
pattern-to-unit expansion and branch updates (cpp:215-234). For length 2^31-1,
the 32-bit threshold is (2*(2^31-1)+2) mod 2^32 = 0, so that first call returns
false before those later operations.

The plugin is installed after several word/regex split plugins and before model
completion in `src\smt\theory_nseq.cpp:205-232`. Earlier propagation/splitting,
literal construction, resource configuration, cancellation and search choices
are NOT proven to leave the required active obligation and select this plugin.
The conditional local control-flow chain is stronger than an invented arbitrary
caller, but is still not an end-to-end reachable native execution trace.

## VERIFY is unconditional and exit policy matters

`src\util\debug.h:108-111` defines VERIFY without a Z3DEBUG guard: false calls
`notify_assertion_violation` and then `invoke_exit_action(ERR_UNREACHABLE)`.
Do not confuse it with SASSERT at line 85. `ERR_UNREACHABLE` is 114
(`src\util\error_codes.h:35`). Notification includes release-build diagnostic
text (`src\util\debug.cpp:74-88`). `invoke_exit_action` is noreturn: its initial
default action is exit(code), and its configured exception action throws a
default_exception("unreachable") (debug.cpp:117-146). `Z3_mk_context_rc` selects
the exception action (`src\api\api_context.cpp:416-423`); do not generalize that
setting to every context or client, or assume where an exception is caught.

Accordingly the source-conditional consequence is an assertion/error exit or
exception if this first-case failure is reached, NOT proven memory corruption,
an observed crash, a debug-only assertion, or a release path that continues
with an uninitialized edge. Batch-2's original guarded admission model remains
unchanged and correctly labeled conditional.

## Evidence and next stage

`capture_nfv3_p12.py` captures exact numbered excerpts and immutable blob/SHA-256
identities in `nfv3-p12-source-inventory.json` using one bounded Git object batch.
Every captured file is checked against the worktree as text. No external tools
or native source execute. This handoff and inventory are for eventual batch-3
publication, not modifications to either immutable published report.

Finish only `nfv3-trace-p12` now. Next ready stage is `nfv3-coverage`, refining
remaining C10/C11/C12 candidates from the existing ledger, not rerunning the
unchanged 89-file classification. Selection must wait for that independent
prerequisite. No new selected properties or positive/negative proof counts are
added by this source follow-up. Keep continuous schedule #2 active.
