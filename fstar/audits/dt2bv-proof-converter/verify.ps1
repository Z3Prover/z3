param(
    [Parameter(Mandatory = $true)][string]$FStar,
    [string]$Z3
)

$ErrorActionPreference = 'Stop'
$root = (Resolve-Path (Join-Path $PSScriptRoot '..\..\..')).Path
if (-not $Z3) { $Z3 = Join-Path $root 'build\z3.exe' }
$FStar = (Resolve-Path $FStar).Path
$Z3 = (Resolve-Path $Z3).Path
$sources = @(
    'src\ast\converters\proof_converter.h',
    'src\ast\converters\proof_converter.cpp',
    'src\ast\rewriter\enum2bv_rewriter.h',
    'src\ast\rewriter\enum2bv_rewriter.cpp',
    'src\tactic\bv\CMakeLists.txt',
    'src\tactic\bv\dt2bv_proof_converter.h',
    'src\tactic\bv\dt2bv_proof_converter.cpp',
    'src\tactic\bv\dt2bv_tactic.cpp',
    'src\tactic\goal.h',
    'src\tactic\goal.cpp',
    'src\tactic\tactic.cpp',
    'src\tactic\tactical.cpp',
    'src\tactic\core\split_clause_tactic.cpp',
    'src\test\get_consequences.cpp'
)
$audit = @('Dt2BvProofConverter.fst', 'REPORT.md', 'verify.ps1')

function Get-Entries([string]$base, [string[]]$paths) {
    foreach ($path in $paths) {
        $text = [System.Text.Encoding]::UTF8.GetString([System.IO.File]::ReadAllBytes((Join-Path $base $path)))
        $bytes = [System.Text.Encoding]::UTF8.GetBytes($text.Replace("`r`n", "`n"))
        $hasher = [System.Security.Cryptography.SHA256]::Create()
        try {
            $hash = [System.BitConverter]::ToString($hasher.ComputeHash($bytes)).Replace('-', '').ToLowerInvariant()
        }
        finally { $hasher.Dispose() }
        [ordered]@{
            name = $path
            sha256 = $hash
        }
    }
}

$beforeSources = @(Get-Entries $root $sources)
$beforeAudit = @(Get-Entries $PSScriptRoot $audit)
$base = (& git -C $root rev-parse HEAD).Trim()
if ($LASTEXITCODE -ne 0) { throw 'Cannot determine base commit' }
$fstarVersion = (& $FStar --version 2>&1 | Out-String).Trim()
if ($LASTEXITCODE -ne 0) { throw 'Cannot determine F* version' }
$z3Version = (& $Z3 --version 2>&1 | Out-String).Trim()
if ($LASTEXITCODE -ne 0 -or $z3Version -notmatch 'Z3 version (\d+\.\d+\.\d+)') {
    throw 'Cannot determine Z3 version'
}
$version = $Matches[1]
$manifestPath = Join-Path $PSScriptRoot 'manifest.json'
if (Test-Path $manifestPath) { Remove-Item -LiteralPath $manifestPath }
$module = Join-Path $PSScriptRoot 'Dt2BvProofConverter.fst'
$output = @(& $FStar --message_format human --warn_error '@1..999' --smt $Z3 --z3version $version $module 2>&1)
$verificationExit = $LASTEXITCODE
$log = Join-Path $PSScriptRoot 'verification.log'
@($fstarVersion, $z3Version, 'Command: F* --message_format human --warn_error @1..999 --smt Z3 --z3version <detected> Dt2BvProofConverter.fst') + $output |
    Set-Content -Encoding utf8 $log
if ($verificationExit -ne 0) { throw "F* verification failed with exit code $verificationExit" }
$afterSources = @(Get-Entries $root $sources)
$afterAudit = @(Get-Entries $PSScriptRoot $audit)
if (($beforeSources | ConvertTo-Json) -cne ($afterSources | ConvertTo-Json) -or
    ($beforeAudit | ConvertTo-Json) -cne ($afterAudit | ConvertTo-Json)) {
    throw 'Source or audit files changed during verification'
}
$manifest = [ordered]@{
    base_sha = $base
    verdict = 'proved-conditional-denotational-transport'
    scope = 'Semantic source audit; not mechanized C++ or SMT correctness'
    hash_normalization = 'UTF-8 text bytes with CRLF normalized to LF, matching Git text blobs'
    toolchain = [ordered]@{
        fstar_version = $fstarVersion
        z3_version = $z3Version
        fstar_sha256 = (Get-FileHash -Algorithm SHA256 $FStar).Hash.ToLowerInvariant()
        z3_sha256 = (Get-FileHash -Algorithm SHA256 $Z3).Hash.ToLowerInvariant()
    }
    sources = $afterSources
    files = @(Get-Entries $PSScriptRoot ($audit + 'verification.log'))
}
$manifest | ConvertTo-Json -Depth 6 | Set-Content -Encoding utf8 $manifestPath
$output
