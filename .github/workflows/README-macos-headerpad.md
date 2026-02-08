# macOS Dylib Header Padding Validation

## Background

Release 4.15.5 broke `install_name_tool` on macOS with "larger updated load commands do not fit" errors. The Mach-O dylib headers lacked sufficient padding for install name modifications.

See:
- Issue: https://github.com/Z3Prover/z3/issues/8532
- Fix: https://github.com/Z3Prover/z3/pull/8535

## The Problem

macOS dynamic libraries (dylibs) have a Mach-O header that includes "load commands" specifying various metadata, including the library's install name. Tools like `install_name_tool` can modify these load commands to change paths.

However, if the header doesn't have sufficient padding, modifying the install name to a longer path will fail with:
```
error: changing install names or rpaths can't be redone for: libz3.dylib (for architecture arm64) 
because larger updated load commands do not fit (the program must be relinked, 
and you may need to use -headerpad or -headerpad_max_install_names)
```

This breaks tools like [setup-z3](https://github.com/cda-tum/setup-z3) which need to modify the install name to absolute paths in CI environments.

## The Solution

### Build-Time Fix
The Z3 build system now unconditionally adds `-Wl,-headerpad_max_install_names` when building shared libraries on macOS:
- **Python build system**: Modified `scripts/mk_util.py` to apply the flag unconditionally (not just when ML bindings are enabled)
- **CMake build system**: Added `target_link_options` to all macOS shared libraries (libz3, z3java, z3jl, OCaml bindings)

### Validation Jobs

To prevent this issue from recurring, we've added validation jobs to the CI/CD pipeline that test whether `install_name_tool` can successfully modify the dylib install names.

#### Workflows with Validation

1. **nightly.yml** - Nightly builds
   - `validate-macos-headerpad-x64`: Validates x64 macOS builds
   - `validate-macos-headerpad-arm64`: Validates ARM64 macOS builds
   - These jobs run after the build stage and before deployment

2. **release.yml** - Release builds  
   - `validate-macos-headerpad-x64`: Validates x64 macOS builds
   - `validate-macos-headerpad-arm64`: Validates ARM64 macOS builds
   - These jobs run after the build stage and before publication

3. **nightly-validation.yml** - Post-deployment validation
   - `validate-macos-headerpad-x64`: Validates published x64 builds
   - `validate-macos-headerpad-arm64`: Validates published ARM64 builds
   - These jobs run after releases are published to verify the artifacts

#### How Validation Works

Each validation job:
1. Downloads the macOS build artifact
2. Extracts the zip file and locates `libz3.dylib`
3. Uses `otool -D` to read the current install name
4. Attempts to change the install name to a long path similar to what setup-z3 uses:
   ```
   /Users/runner/hostedtoolcache/z3/latest/x64/z3-4.15.5-x64-osx-15.7.3/bin/libz3.dylib
   ```
5. Verifies the change succeeded
6. Fails the build if headerpad is insufficient

#### Test Path Selection

The validation uses paths that match the length and structure of real-world usage by setup-z3:
- x64: `/Users/runner/hostedtoolcache/z3/latest/x64/z3-test-dir/bin/libz3.dylib`
- ARM64: `/Users/runner/hostedtoolcache/z3/latest/arm64/z3-test-dir/bin/libz3.dylib`

These paths are representative of the GitHub Actions hosted tool cache paths that would be used in practice.

## Impact

With these validations in place:
- Releases with insufficient header padding will fail CI before publication
- Users won't encounter `install_name_tool` errors when using Z3 in CI
- The issue can be detected and fixed immediately during development

## References

- Original issue: https://github.com/Z3Prover/z3/issues/8532
- Fix PR: https://github.com/Z3Prover/z3/pull/8535
- Previous similar issue: https://github.com/Z3Prover/z3/pull/7623
- setup-z3 action: https://github.com/cda-tum/setup-z3
