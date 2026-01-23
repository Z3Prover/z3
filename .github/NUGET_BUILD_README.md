# NuGet Package Build Workflow

This document describes the GitHub Actions workflow for building Z3 NuGet packages.

## Overview

The NuGet build workflow (`.github/workflows/nuget-build.yml`) creates Microsoft.Z3 NuGet packages for distribution. It builds Z3 for all supported platforms and assembles them into NuGet packages.

## Triggering the Workflow

The workflow can be triggered in two ways:

### 1. Manual Trigger

You can manually trigger the workflow from the GitHub Actions tab:

1. Go to the "Actions" tab in the repository
2. Select "Build NuGet Package" workflow
3. Click "Run workflow"
4. Enter the version number (e.g., `4.15.5`)
5. Click "Run workflow"

### 2. Tag-based Trigger

The workflow automatically runs when you push a tag with the `z3-` prefix:

```bash
git tag z3-4.15.5
git push origin z3-4.15.5
```

## Workflow Structure

The workflow consists of multiple jobs:

### Build Jobs

1. **build-windows-x64**: Builds Windows x64 binaries with .NET support
2. **build-windows-x86**: Builds Windows x86 binaries with .NET support
3. **build-windows-arm64**: Builds Windows ARM64 binaries with .NET support
4. **build-ubuntu**: Builds Linux x64 binaries with .NET support
5. **build-macos-x64**: Builds macOS x64 binaries with .NET support
6. **build-macos-arm64**: Builds macOS ARM64 binaries with .NET support

### Package Jobs

1. **package-nuget-x64**: Creates the main NuGet package (Microsoft.Z3.nupkg) with x64, ARM64, Linux, and macOS support
2. **package-nuget-x86**: Creates the x86 NuGet package (Microsoft.Z3.x86.nupkg)

## Output

The workflow produces two NuGet packages as artifacts:

- `Microsoft.Z3.{version}.nupkg` and `Microsoft.Z3.{version}.snupkg` (x64 + multi-platform)
- `Microsoft.Z3.x86.{version}.nupkg` and `Microsoft.Z3.x86.{version}.snupkg` (x86 only)

These can be downloaded from the workflow run's artifacts section.

## Key Files

- `.github/workflows/nuget-build.yml`: The workflow definition
- `scripts/mk_nuget_task.py`: Script that assembles the NuGet package from build artifacts
- `scripts/mk_win_dist.py`: Script for building Windows x86/x64 distributions
- `scripts/mk_win_dist_cmake.py`: Script for building Windows ARM64 distributions
- `scripts/mk_unix_dist.py`: Script for building Linux and macOS distributions

## Bug Fix

This workflow includes a fix for a critical bug in `mk_nuget_task.py` where the `replace()` function had incorrect logic that would fail to copy files when the destination already existed. The fix ensures that Microsoft.Z3.dll and related files are always properly included in the NuGet package under `lib/netstandard2.0/`.

## Development

To test changes to the NuGet packaging locally, you can:

1. Build the platform-specific binaries using the appropriate build scripts
2. Collect the resulting ZIP files in a directory
3. Run `mk_nuget_task.py` to assemble the package:

```bash
python scripts/mk_nuget_task.py <packages_dir> <version> <repo_url> <branch> <commit> <source_dir> [symbols] [x86]
```

4. Use the NuGet CLI to pack the package:

```bash
nuget pack out/Microsoft.Z3.sym.nuspec -OutputDirectory . -Verbosity detailed -Symbols -SymbolPackageFormat snupkg -BasePath out
```
