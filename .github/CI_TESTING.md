# Testing the CI Workflow

This document provides instructions for testing the new GitHub Actions CI workflow after migration from Azure Pipelines.

## Quick Test

To test the workflow:

1. **Push a branch or create a PR**: The workflow automatically triggers on all branches
2. **View workflow runs**: Go to the "Actions" tab in GitHub
3. **Monitor progress**: Click on a workflow run to see job details

## Manual Trigger

You can also manually trigger the workflow:

1. Go to the "Actions" tab
2. Select "CI" from the left sidebar
3. Click "Run workflow"
4. Choose your branch
5. Click "Run workflow"

## Local Validation

Before pushing, you can validate the YAML syntax locally:

```bash
# Using yamllint (install with: pip install yamllint)
yamllint .github/workflows/ci.yml

# Using Python PyYAML
python3 -c "import yaml; yaml.safe_load(open('.github/workflows/ci.yml'))"

# Using actionlint (install from https://github.com/rhysd/actionlint)
actionlint .github/workflows/ci.yml
```

## Job Matrix

The CI workflow includes these job categories:

### Linux Jobs
- **linux-python-debug**: Python-based build with make (MT and ST variants)
- **manylinux-python-amd64**: Python wheel build for manylinux AMD64
- **manylinux-python-arm64**: Python wheel build for manylinux ARM64 (cross-compile)
- **ubuntu-ocaml**: OCaml bindings build
- **ubuntu-ocaml-static**: OCaml static library build
- **ubuntu-cmake**: CMake builds with multiple compilers (4 variants)

### macOS Jobs
- **macos-python**: Python-based build with make
- **macos-cmake**: CMake build with Julia support

## Expected Runtime

Approximate job durations:
- Linux Python builds: 20-30 minutes
- Manylinux Python builds: 15-25 minutes
- OCaml builds: 25-35 minutes
- CMake builds: 25-35 minutes each variant
- macOS builds: 30-40 minutes

Total workflow time (all jobs in parallel): ~40-60 minutes

## Debugging Failed Jobs

If a job fails:

1. **Click on the failed job** to see the log
2. **Expand failed steps** to see detailed output
3. **Check for common issues**:
   - Missing dependencies
   - Test failures
   - Build errors
   - Timeout (increase timeout-minutes if needed)

4. **Re-run failed jobs**:
   - Click "Re-run failed jobs" button
   - Or "Re-run all jobs" to test everything

## Comparing with Azure Pipelines

To compare results:

1. Check the last successful Azure Pipelines run
2. Compare job names and steps with the GitHub Actions workflow
3. Verify all tests pass with similar coverage

## Differences from Azure Pipelines

1. **Checkout**: Explicit `actions/checkout@v4` step (was implicit)
2. **Python Setup**: Explicit `actions/setup-python@v5` step (was implicit)
3. **Template Files**: Inlined instead of external templates
4. **Artifacts**: Uses `actions/upload-artifact` (if needed in future)
5. **Caching**: Can add `actions/cache` for dependencies (optional optimization)

## Adding Jobs or Modifying

To add or modify jobs:

1. Edit `.github/workflows/ci.yml`
2. Follow the existing job structure
3. Use matrix strategy for variants
4. Add appropriate timeouts (default: 90 minutes)
5. Test your changes on a branch first

## Optimization Opportunities

Future optimizations to consider:

1. **Caching**: Add dependency caching (npm, pip, opam, etc.)
2. **Artifacts**: Share build artifacts between jobs
3. **Concurrency**: Add concurrency groups to cancel outdated runs
4. **Selective Execution**: Skip jobs based on changed files
5. **Self-hosted Runners**: For faster builds (if available)

## Rollback Plan

If the GitHub Actions workflow has issues:

1. The original `azure-pipelines.yml` is still in the repository
2. Azure Pipelines can be re-enabled if needed
3. Both systems can run in parallel during transition

## Support

For issues or questions:

1. Check GitHub Actions documentation: https://docs.github.com/en/actions
2. Review the migration document: `.github/workflows/CI_MIGRATION.md`
3. Check existing GitHub Actions workflows in `.github/workflows/`
4. Open an issue in the repository
