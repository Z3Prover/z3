<#
.SYNOPSIS
  Builds the standalone, self-contained native proof-checker executable
  described in fstar/OCAML_CHECKER_REPORT.md.

.DESCRIPTION
  This is a two-phase pipeline:

    Phase 1 (Windows, fstar.exe): type-check the equational and resolution
    JSON checkers and their dependencies, caching a `.checked` file per module
    (fstar.exe's OCaml-extraction backend requires every module --
    including the one being extracted, not just its dependencies -- to
    already have a `.checked` file on disk, so this is done bottom-up,
    one module at a time). Then re-invoke
    fstar.exe with `--codegen OCaml` against those caches to produce a
    plain `.ml` file per module under `--odir`.

    Phase 2 (WSL, ocamlfind ocamlopt): compile those extracted `.ml`
    files together with this project's own hand-written runtime shim
    (`fstar/ocaml_runtime/*.ml` -- see OCAML_CHECKER_REPORT.md for why a
    hand-written shim is used instead of linking the bundled
    `fstar.cmxa`) and `main.ml` (the stdin/file CLI wrapper) into one
    native executable, with no F*/fstar.exe/SMT-solver involvement at
    all at proof-checking time.

  Requires (see OCAML_CHECKER_REPORT.md "Reproducing the build" for the
  one-time setup of these):
    - fstar.exe and a matching z3 on this Windows machine (same ones
      used everywhere else in this repo).
    - WSL with an opam switch named 'fstar53' using OCaml 5.3.0 (the
      OCaml release whose `.cmi` magic number matches this F*
      distribution's own build -- see the report for how this was
      determined; no opam packages beyond the compiler itself are
      required, since the hand-written runtime shim has zero external
      dependencies).

.PARAMETER WslBuildDir
  Where to copy the built executable *inside WSL* (default:
  ~/z3checker/checker). Printed at the end as a `wsl <path>` command.

.PARAMETER CacheDir
  Optional existing F* cache directory. Modules are still checked for
  source/dependency changes before extraction.
#>
param(
  [string]$FstarExe = "C:\fstar\fstar\bin\fstar.exe",
  [string]$Z3Exe = "C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe",
  [string]$OpamSwitch = "fstar53",
  [string]$WslBuildDir = "~/z3checker",
  [string]$CacheDir = ""
)

$ErrorActionPreference = "Continue"
$fstarDir = Split-Path -Parent $PSScriptRoot  # .../fstar
Push-Location $fstarDir
try {
  if (-not $CacheDir) { $CacheDir = Join-Path $fstarDir "build_cache" }
  $extractDir = Join-Path $fstarDir "build_extract"
  New-Item -ItemType Directory -Force -Path $CacheDir | Out-Null
  New-Item -ItemType Directory -Force -Path $extractDir | Out-Null

  # Dependencies must be cached before their dependents are extracted.
  $modules = @(
    "Z3AstTheory.fst", "Z3ArrayTheory.fst", "Z3SeqTheory.fst", "Z3BvTheory.fst",
    "Z3ValueTheory.fst", "Z3ProofTheory.fst", "Z3ArrayInterp.fst",
    "Z3SeqInterp.fst", "Z3BvInterp.fst", "Z3BoolRewriter.fst", "Z3BvRewriter.fst",
    "Z3SeqRewrites.fst", "Z3InterpretedProofChecker.fst",
    "Z3PatternMatchedProofChecker.fst", "Z3PulseProofChecker.fst",
    "Z3ProofJson.fst", "Z3PulseProofCheckerJson.fst",
    "Z3ResolutionProofTheory.fst", "Z3ObservationalEquality.fst",
    "Z3BasicExprTheory.fst", "Z3BoundedBoolEquiv.fst", "Z3BooleanNormalForm.fst",
    "Z3Commutativity.fst", "Z3BooleanRewrite.fst", "Z3ArrayLemma.fst",
    "Z3UnifiedProof.fst", "Z3ResolutionProofJson.fst"
  )

  Write-Host "=== Phase 1a: type-check + cache ==="
  foreach ($f in $modules) {
    & $FstarExe --cache_checked_modules --cache_dir $CacheDir --include $CacheDir --smt $Z3Exe $f 2>&1 |
      ForEach-Object { Write-Host $_ }
    if ($LASTEXITCODE -ne 0) { throw "F* verification failed: $f" }
  }
  $missing = $modules | Where-Object { -not (Test-Path (Join-Path $CacheDir ($_ -replace '\.fst$', '.fst.checked'))) }
  if ($missing) { throw "Failed to cache: $($missing -join ', ')" }

  Write-Host "=== Phase 1b: extract to OCaml ==="
  $modNames = ($modules | ForEach-Object { $_ -replace '\.fst$', '' }) -join " "
  foreach ($root in @("Z3PulseProofCheckerJson.fst", "Z3ResolutionProofJson.fst")) {
    & $FstarExe --codegen OCaml --cache_dir $CacheDir --include $CacheDir --odir $extractDir `
        --extract $modNames $root
    if ($LASTEXITCODE -ne 0) { throw "OCaml extraction failed: $root" }
  }

  Write-Host "=== Phase 2: compile in WSL ==="
  $drive = $fstarDir.Substring(0, 1).ToLowerInvariant()
  $wslFstarDir = "/mnt/$drive/" + $fstarDir.Substring(3).Replace('\', '/')
  $order = @(
    "prims.ml", "fStar_Pervasives_Native.ml", "fStar_List_Tot_Base.ml", "fStar_Char.ml",
    "fStar_UInt32.ml", "fStar_UInt.ml", "fStar_String.ml", "fStar_FunctionalExtensionality.ml",
    "pulse_Lib_Reference.ml", "pulse_Lib_Dv.ml",
    "Z3AstTheory.ml", "Z3ArrayTheory.ml", "Z3SeqTheory.ml", "Z3BvTheory.ml", "Z3ValueTheory.ml",
    "Z3ProofTheory.ml", "Z3BoolRewriter.ml", "Z3BvRewriter.ml", "Z3SeqRewrites.ml",
    "Z3BvInterp.ml", "Z3SeqInterp.ml", "Z3ArrayInterp.ml", "Z3InterpretedProofChecker.ml",
    "Z3PatternMatchedProofChecker.ml", "Z3PulseProofChecker.ml", "Z3ProofJson.ml",
    "Z3PulseProofCheckerJson.ml", "Z3ResolutionProofTheory.ml", "Z3ObservationalEquality.ml",
    "Z3BasicExprTheory.ml", "Z3BoundedBoolEquiv.ml", "Z3BooleanNormalForm.ml",
    "Z3Commutativity.ml", "Z3BooleanRewrite.ml", "Z3ArrayLemma.ml", "Z3UnifiedProof.ml",
    "Z3ResolutionProofJson.ml", "main.ml"
  )
  $orderStr = $order -join " "
  $script = @"
set -e
export PATH="`$HOME/bin:`$PATH"
mkdir -p $WslBuildDir
cp "$wslFstarDir"/ocaml_runtime/*.ml $WslBuildDir/
cp "$wslFstarDir"/build_extract/*.ml $WslBuildDir/
cd $WslBuildDir
eval `$(opam env --switch=$OpamSwitch)
ocamlfind ocamlopt $orderStr -o checker
echo BUILD_OK
"@
  $scriptPath = Join-Path $fstarDir "build_wsl_tmp.sh"
  $unixScript = $script -replace "`r`n", "`n"
  [System.IO.File]::WriteAllText($scriptPath, $unixScript, (New-Object System.Text.UTF8Encoding($false)))
  wsl -e bash "$wslFstarDir/build_wsl_tmp.sh"
  Remove-Item $scriptPath -ErrorAction SilentlyContinue
  if ($LASTEXITCODE -ne 0) { throw "WSL compile failed" }

  Write-Host "=== Done. Run with: wsl $WslBuildDir/checker [path/to/proof.json] ==="
}
finally {
  Pop-Location
}
