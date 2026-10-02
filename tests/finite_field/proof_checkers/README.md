# External checker pins

`versions.json` records the public companion sources used for the Alethe/PAC
pipeline, their exact archive checksums, and the local FFPacheck patch checksum.
These are public repository revisions, **not a claim of byte identity with the
binaries inside the Zenodo virtual machine**. No dependency is added to Z3.
Carcara remains unmodified; FFPacheck requires the recorded patch.

Build outside the tracked source tree (GMP, CMake, a C++20 compiler and Rust are
required). Download each `archive` URL in `versions.json`, verify its `sha256`,
and extract each into a separate directory using `tar --strip-components=1`.
From the extracted Carcara directory:

```sh
cargo build --release --locked
```

From the extracted FFPacheck directory, with `Z3_SOURCE` set to this checkout:

```sh
patch -p1 < "$Z3_SOURCE/tests/finite_field/proof_checkers/ffpacheck-completion.patch"
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j4
```

On macOS, GMP may require `-DCMAKE_PREFIX_PATH="$(brew --prefix gmp)"` and
`-DCMAKE_CXX_FLAGS="-I$(brew --prefix gmp)/include"`. Use a compiler and SDK from
the same Xcode/Command Line Tools installation; select an SDK explicitly with
`-DCMAKE_OSX_SYSROOT` if necessary. The tested build used AppleClang 21, the
Xcode macOS 26.5 SDK, and Homebrew GMP. The Cargo lockfile and the source's
Rust 1.87 toolchain pin were honored.

The executables are `target/release/carcara` and `build/ffpacheck`. Use those
paths with `scripts/ff_proof_pipeline.py`, then run
`tests/finite_field/test_ff_proof_pipeline.py` with all three executable paths.

## Why the patch and the input guard are required

At the pinned FFPacheck revision, `closeCurrentBranch` returns immediately at
depth zero, even for a checked derivation of 1. The patch marks the proof complete
when there are no pending root domains. It also rejects EOF without completion;
the original `main` prints success unconditionally at EOF. The added `<sstream>`
include fixes a missing direct include exposed by libc++.

The upstream 503-file suite with this patch yields 498 passes and 5 rejections
of files labelled valid: `with_uf/with_uf5_{1,2,3,6,11}.proof`. Each of these five
files contains only the modulus and 22 axioms, with no derivation or completion
step. They are rejected intentionally by the strengthened completion contract.
All 22 files under `faulty_proofs` remain rejected.

The pinned Carcara `ff_pac` rule passes its raw PAC payload to FFPacheck, without
checking that its axioms, field and variable map correspond to the rule's
premise, or validating the conclusion. The pipeline test reproduces acceptance
of an unrelated PAC contradiction against a satisfiable SMT problem. Therefore
**raw Carcara acceptance is not the acceptance contract of this pipeline**.
The independent original-input/DAG check and exact exported-byte binding are
mandatory. Do not use `--allow-rule`, holes, or unknown-rule admission.

These findings concern the inspected public revisions. No upstream issue has
been submitted, and the contents of the artifact image have not been audited.
