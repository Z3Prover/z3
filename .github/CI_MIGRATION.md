# Azure Pipelines to GitHub Actions Migration

## Overview

This document describes the migration from Azure Pipelines (`azure-pipelines.yml`) to GitHub Actions (`.github/workflows/ci.yml`).

## Migration Summary

All jobs from the Azure Pipelines configuration have been migrated to GitHub Actions with equivalent or improved functionality.

### Jobs Migrated

| Azure Pipelines Job | GitHub Actions Job | Status |
|---------------------|-------------------|--------|
| LinuxPythonDebug (MT) | linux-python-debug (MT) | ✅ Migrated |
| LinuxPythonDebug (ST) | linux-python-debug (ST) | ✅ Migrated |
| ManylinuxPythonBuildAmd64 | manylinux-python-amd64 | ✅ Migrated |
| ManyLinuxPythonBuildArm64 | manylinux-python-arm64 | ✅ Migrated |
| UbuntuOCaml | ubuntu-ocaml | ✅ Migrated |
| UbuntuOCamlStatic | ubuntu-ocaml-static | ✅ Migrated |
| UbuntuCMake (releaseClang) | ubuntu-cmake (releaseClang) | ✅ Migrated |
| UbuntuCMake (debugClang) | ubuntu-cmake (debugClang) | ✅ Migrated |
| UbuntuCMake (debugGcc) | ubuntu-cmake (debugGcc) | ✅ Migrated |
| UbuntuCMake (releaseSTGcc) | ubuntu-cmake (releaseSTGcc) | ✅ Migrated |
| MacOSPython | macos-python | ✅ Migrated |
| MacOSCMake | macos-cmake | ✅ Migrated |
| LinuxMSan | N/A | ⚠️ Was disabled (condition: eq(0,1)) |
| MacOSOCaml | N/A | ⚠️ Was disabled (condition: eq(0,1)) |

## Key Differences

### Syntax Changes

1. **Trigger Configuration**
   - Azure: `jobs:` with implicit triggers
   - GitHub: Explicit `on:` section with `push`, `pull_request`, and `workflow_dispatch`

2. **Job Names**
   - Azure: `displayName` field
   - GitHub: `name` field

3. **Steps**
   - Azure: `script:` for shell commands
   - GitHub: `run:` for shell commands

4. **Checkout**
   - Azure: Implicit checkout
   - GitHub: Explicit `uses: actions/checkout@v4`

5. **Python Setup**
   - Azure: Implicit Python availability
   - GitHub: Explicit `uses: actions/setup-python@v5`

6. **Variables**
   - Azure: Top-level `variables:` section
   - GitHub: Inline in job steps or matrix configuration

### Template Scripts

Azure Pipelines used external template files (e.g., `scripts/test-z3.yml`, `scripts/test-regressions.yml`). These have been inlined into the GitHub Actions workflow:

- `scripts/test-z3.yml`: Unit tests → Inlined as "Run unit tests" step
- `scripts/test-regressions.yml`: Regression tests → Inlined as "Run regressions" step
- `scripts/test-examples-cmake.yml`: CMake examples → Inlined as "Run examples" step
- `scripts/generate-doc.yml`: Documentation → Inlined as "Generate documentation" step

### Matrix Strategies

Both Azure Pipelines and GitHub Actions support matrix builds. The migration maintains the same matrix configurations:

- **linux-python-debug**: 2 variants (MT, ST)
- **ubuntu-cmake**: 4 variants (releaseClang, debugClang, debugGcc, releaseSTGcc)

### Container Jobs

Manylinux builds continue to use container images:
- `quay.io/pypa/manylinux_2_34_x86_64:latest` for AMD64
- `quay.io/pypa/manylinux2014_x86_64:latest` for ARM64 cross-compilation

### Disabled Jobs

Two jobs were disabled in Azure Pipelines (with `condition: eq(0,1)`) and have not been migrated:
- **LinuxMSan**: Memory sanitizer builds
- **MacOSOCaml**: macOS OCaml builds

These can be re-enabled in the future if needed by adding them to the workflow file.

## Benefits of GitHub Actions

1. **Unified Platform**: All CI/CD in one place (GitHub)
2. **Better Integration**: Native integration with GitHub features (checks, status, etc.)
3. **Actions Marketplace**: Access to pre-built actions
4. **Improved Caching**: Better artifact and cache management
5. **Cost**: Free for public repositories

## Testing

To test the new workflow:

1. Push a branch or create a pull request
2. The workflow will automatically trigger
3. Monitor progress in the "Actions" tab
4. Review job logs for any issues

## Deprecation Plan

1. ✅ Create new GitHub Actions workflow (`.github/workflows/ci.yml`)
2. 🔄 Test and validate the new workflow
3. ⏳ Run both pipelines in parallel for a transition period
4. ⏳ Once stable, deprecate `azure-pipelines.yml`

## Rollback Plan

If issues arise with the GitHub Actions workflow:
1. The original `azure-pipelines.yml` remains in the repository
2. Azure Pipelines can be re-enabled if needed
3. Both can run in parallel during the transition

## Additional Resources

- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [Migrating from Azure Pipelines to GitHub Actions](https://docs.github.com/en/actions/migrating-to-github-actions/migrating-from-azure-pipelines-to-github-actions)
- [GitHub Actions Syntax Reference](https://docs.github.com/en/actions/reference/workflow-syntax-for-github-actions)
