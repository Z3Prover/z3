<#
.SYNOPSIS
Verify the SQL formalization and run its independent SQLite regressions.
.EXAMPLE
.\fstar\tools\verify_sql.ps1 -FstarExe C:\fstar\fstar\bin\fstar.exe
#>
param(
    [string]$FstarExe = "fstar.exe",
    [string]$Z3Exe = "",
    [string]$CacheDir = "",
    [switch]$Refresh
)

$ErrorActionPreference = "Stop"
$root = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$sources = Join-Path $root "fstar"
if (-not $Z3Exe) { $Z3Exe = Join-Path $root "build\z3.exe" }
if (-not $CacheDir) { $CacheDir = Join-Path $root "build\fstar-sql-cache" }
$Z3Exe = (Resolve-Path $Z3Exe).Path
$versionOutput = & $Z3Exe --version
if ($LASTEXITCODE -ne 0 -or $versionOutput -notmatch 'Z3 version (\S+)') {
    throw "Cannot determine Z3 version: $versionOutput"
}
$version = $Matches[1]
New-Item -ItemType Directory -Force $CacheDir | Out-Null
$flags = @(
    "--smt", $Z3Exe, "--z3version", $version,
    "--include", $sources, "--cache_checked_modules", "--cache_dir", $CacheDir,
    "--already_cached", "Prims,FStar", "--warn_error", "+241"
)
if ($Refresh) { $flags += "--z3refresh" }
& $FstarExe --version
if ($LASTEXITCODE -ne 0) { throw "Cannot execute F*: $FstarExe" }
Write-Host "SMT backend: $Z3Exe ($version)"
foreach ($module in @("Sql.Core.fst", "Sql.Query.fst", "Sql.Laws.fst",
                     "Sql.Examples.fst", "Sql.Tests.fst", "Sql.Optimize.fst",
                     "Sql.Native.fsti", "Sql.Cherry.fst")) {
    & $FstarExe @flags (Join-Path $sources $module)
    if ($LASTEXITCODE -ne 0) { throw "F* verification failed: $module" }
}
& python (Join-Path $PSScriptRoot "test_sql_semantics.py")
if ($LASTEXITCODE -ne 0) { throw "SQLite regression tests failed" }
