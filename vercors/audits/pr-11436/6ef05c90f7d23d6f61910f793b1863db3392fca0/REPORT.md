# VerCors C++ audit, PR #11436, head 6ef05c90f7d23d6f61910f793b1863db3392fca0 (base c95b61cb03b22e258dfbc5941262c9273e6650bd)

Source: fstar/cherry_runtime/main.cpp at head, sha256 668ae40f03994e7601a9fc2b694c81da2abbf77aedba0935f2ea46dda99d222d (687 lines), fetched via the contents API.
Tools: VerCors 2.4.0, silicon backend, bundled Z3, Java as installed in the runner.

## Selected function
`run(argc, argv)` (option parsing), lines 591-595 and 620-621. One C++ function was selected. The only other changed C++ hunk is in `check_proof` (L342-355) and is excluded.

## Obligations
1. parse_tstp (L591-595): after `--tstp-out`, the next index must exist and the path must be non-empty. Otherwise the code throws and leaves options.tstp_out unchanged. On success it consumes exactly argv[i+1] and sets tstp_out non-empty. **Proved.**
2. post_check (L620-621): `--tstp-out` combined with `--interactive` or `--clause-proofs` is rejected, and every other combination is accepted. **Proved.**
3. Non-vacuity: witness units `witness_ok` and `witness_missing` use concrete argv models and pass. They show a success path, a missing-path error, and both rejection cases.

## Correspondence and abstractions (manual)
- argv strings are modelled as an int array holding each string's first character (0 means empty). `*argv[i]` becomes `first[i] != 0`.
- `NativeError` throws are modelled as return -1 with no mutation.
- `options.tstp_out` is modelled as an int flag (1 means non-empty).
- Booleans are ints. No arithmetic beyond i+1 is used. argc > 0 and i < argc are caller preconditions (loop bounds `i < argc`). int overflow on i+1 is excluded by i < argc.
- Pointer permissions: argv read-only fractional (1\2) and flag write. These are justified environment preconditions.

## Exclusions
- check_proof L342-355 export block: it calls Z3Cherry_tstp, std::ofstream, and cherry refcounting. These are not expressible in VerCors C++ without invented contracts.
- Std::string handling, `std::from_chars`, the usage string, and all other hunks (F*, OCaml, Python, PowerShell, JSON) are out of scope.
- No counterexample was found. This is not a whole-program theorem.
- The earlier failed attempts were annotation errors (NULL not supported, permission syntax) in my own extract and not findings about the PR.

## Reproduce
```
mkdir clean && cd clean && cp TstpOption.cpp .
/tmp/gh-aw/vercors/vercors --lang cpp --backend silicon --dev-total-timeout 60 $PWD/TstpOption.cpp
```
Unit sha256: e9c3538b94146212627e11257568e1fe7c0d757d9ae6355913069aedef6dccbb
