<#
.SYNOPSIS
  Builds the standalone, self-contained native proof-checker executable
  described in fstar/OCAML_CHECKER_REPORT.md.

.DESCRIPTION
  This is a two-phase pipeline:

    Phase 1 (Windows, fstar.exe): type-check the shared typed checker,
    and direct native marshaler, caching a `.checked` file per module
    (fstar.exe's OCaml-extraction backend requires every module --
    including the one being extracted, not just its dependencies -- to
    already have a `.checked` file on disk, so this is done bottom-up,
    one module at a time). Then re-invoke
    fstar.exe with `--codegen OCaml` against those caches to produce a
    plain `.ml` file per module under `--odir`.

    Phase 2 (WSL, CMake + ocamlfind ocamlopt): build static libz3 and
    its official OCaml bindings from this checkout, then compile the extracted `.ml`
    files together with the Z3Native foreign implementation and runtime shim
    (`fstar/ocaml_runtime/*.ml` -- see OCAML_CHECKER_REPORT.md for why a
    hand-written shim is used instead of linking the bundled
    `fstar.cmxa`) and `main.ml` (the stdin/file CLI wrapper) into one
    native executable that solves, marshals, and checks in process
    without Python, JSON, external solver processes, or runtime F* invocation.
    The kernel itself never calls Z3.

  Requires (see OCAML_CHECKER_REPORT.md "Reproducing the build" for the
  one-time setup of these):
    - fstar.exe and a matching z3 on this Windows machine (same ones
      used everywhere else in this repo).
    - WSL with an opam switch named 'fstar53' using OCaml 5.3.0 (the
      OCaml release whose `.cmi` magic number matches this F*
      distribution's own build -- see the report for how this was
      determined), Zarith, CMake, Python 3 for Z3's build-time code
      generation, and a C++20 compiler.

.PARAMETER WslBuildDir
  Where to copy the built executable *inside WSL* (default:
  ~/z3checker/checker). Printed at the end as a `wsl <path>` command.

.PARAMETER CacheDir
  Optional existing F* cache directory. Modules are still checked for
  source/dependency changes before extraction.

.PARAMETER Z3BuildDir
  WSL CMake build directory for the static Z3 library and official OCaml bindings.

.PARAMETER RunTests
  Compile and execute native marshaling, sharing, and typed-checker regressions.
#>
param(
  [string]$FstarExe = "C:\fstar\fstar\bin\fstar.exe",
  [string]$Z3Exe = "C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe",
  [string]$OpamSwitch = "fstar53",
  [string]$WslBuildDir = "~/z3checker",
  [string]$Z3BuildDir = "~/z3-native-ffi-build",
  [string]$CacheDir = "",
  [switch]$RunTests
)

$ErrorActionPreference = "Continue"
$fstarDir = Split-Path -Parent $PSScriptRoot  # .../fstar
Push-Location $fstarDir
try {
  if (-not $CacheDir) { $CacheDir = Join-Path $fstarDir "build_cache" }
  $extractDir = Join-Path $fstarDir "build_extract\native"
  New-Item -ItemType Directory -Force -Path $CacheDir | Out-Null
  New-Item -ItemType Directory -Force -Path $extractDir | Out-Null

  # Dependencies must be cached before their dependents are extracted.
  $modules = @(
    "Z3AstTheory.fst", "Z3ArrayTheory.fst", "Z3SeqTheory.fst", "Z3BvTheory.fst",
    "Z3ValueTheory.fst", "Z3ProofTheory.fst", "Z3ProofIndex.fst",
    "Z3ResolutionProofTheory.fst", "Z3ObservationalEquality.fst",
    "Z3BasicExprTheory.fst", "Z3BoundedBoolEquiv.fst", "Z3BooleanNormalForm.fst",
    "Z3Commutativity.fst", "Z3BooleanRewrite.fst",
    "Z3DistinctAst.fst", "Z3DistinctEmbed.fst", "Z3ArrayLemma.fst",
    "Z3ArrayRewrite.fst", "Z3Definitions.fst",
    "Z3LinearArithmeticTheory.fst", "Z3LinearArithmeticAst.fst", "Z3LinearArithmeticEmbed.fst",
    "Z3UnifiedProof.fst", "Z3ProofDocument.fst",
    "Z3Native.fsti", "Z3NativeProof.fst"
  )

  Write-Host "=== Phase 1a: type-check + cache ==="
  foreach ($f in $modules) {
    & $FstarExe --cache_checked_modules --cache_dir $CacheDir --include $CacheDir --smt $Z3Exe $f 2>&1 |
      ForEach-Object { Write-Host $_ }
    if ($LASTEXITCODE -ne 0) { throw "F* verification failed: $f" }
  }
  $missing = $modules | Where-Object { -not (Test-Path (Join-Path $CacheDir "$_.checked")) }
  if ($missing) { throw "Failed to cache: $($missing -join ', ')" }

  Write-Host "=== Phase 1b: extract to OCaml ==="
  $modNames = ($modules | Where-Object { $_ -ne "Z3Native.fsti" } |
    ForEach-Object { $_ -replace '\.fst$', '' }) -join " "
  & $FstarExe --codegen OCaml --cache_dir $CacheDir --include $CacheDir --odir $extractDir `
      --extract $modNames Z3NativeProof.fst
  if ($LASTEXITCODE -ne 0) { throw "OCaml extraction failed: Z3NativeProof.fst" }

  Write-Host "=== Phase 2: compile in WSL ==="
  $drive = $fstarDir.Substring(0, 1).ToLowerInvariant()
  $wslFstarDir = "/mnt/$drive/" + $fstarDir.Substring(3).Replace('\', '/')
  $order = @(
    "prims.ml", "fStar_Pervasives_Native.ml", "fStar_List_Tot_Base.ml",
    "fStar_UInt.ml", "fStar_FunctionalExtensionality.ml",
    "Z3AstTheory.ml", "Z3ArrayTheory.ml", "Z3SeqTheory.ml", "Z3BvTheory.ml", "Z3ValueTheory.ml",
    "Z3ProofTheory.ml", "Z3ProofIndex.ml",
    "Z3ResolutionProofTheory.ml", "Z3ObservationalEquality.ml",
    "Z3BasicExprTheory.ml", "Z3BoundedBoolEquiv.ml", "Z3BooleanNormalForm.ml",
    "Z3Commutativity.ml", "Z3BooleanRewrite.ml", "Z3DistinctAst.ml", "Z3DistinctEmbed.ml",
    "Z3ArrayLemma.ml", "Z3ArrayRewrite.ml",
    "Z3Definitions.ml", "Z3LinearArithmeticTheory.ml", "Z3LinearArithmeticAst.ml",
    "Z3LinearArithmeticEmbed.ml", "Z3UnifiedProof.ml", "Z3ProofDocument.ml",
    "Z3Native.ml", "Z3NativeProof.ml", "Z3NativeMain.ml", "main.ml"
  )
  $orderStr = $order -join " "
  $testScript = ""
  if ($RunTests) {
    $testOrder = ($order | Where-Object { $_ -ne "main.ml" -and $_ -ne "Z3NativeMain.ml" }) -join " "
    $testScript = @"
cp "$wslFstarDir/tools/test_native_bridge.ml" .
ocamlfind ocamlopt -package zarith,unix -linkpkg -I "`$z3_build/src/api/ml" \
  z3ml.cmxa $testOrder test_native_bridge.ml -o native-tests
./native-tests
"@
  }
  $script = @"
set -e
export PATH="`$HOME/bin:`$PATH"
mkdir -p $WslBuildDir
for module in $orderStr; do
  if [ -f "$wslFstarDir/ocaml_runtime/`$module" ]; then
    cp "$wslFstarDir/ocaml_runtime/`$module" $WslBuildDir/
  else
    cp "$wslFstarDir/build_extract/native/`$module" $WslBuildDir/
  fi
done
cd $WslBuildDir
eval `$(opam env --switch=$OpamSwitch)
z3_build=$Z3BuildDir
cmake -S "$wslFstarDir/.." -B "`$z3_build" -DCMAKE_BUILD_TYPE=Release \
  -DBUILD_SHARED_LIBS=OFF -DZ3_BUILD_OCAML_BINDINGS=ON \
  -DZ3_BUILD_EXECUTABLE=OFF -DZ3_BUILD_TEST_EXECUTABLES=OFF -DZ3_INSTALL_OCAML_BINDINGS=OFF
cmake --build "`$z3_build" --parallel 16
ocamlfind ocamlopt -package zarith,unix -linkpkg -I "`$z3_build/src/api/ml" \
  z3ml.cmxa $orderStr -o checker
$testScript
echo BUILD_OK
"@
  $scriptPath = Join-Path $fstarDir "build_wsl_tmp.sh"
  $unixScript = $script -replace "`r`n", "`n"
  [System.IO.File]::WriteAllText($scriptPath, $unixScript, (New-Object System.Text.UTF8Encoding($false)))
  wsl -e bash "$wslFstarDir/build_wsl_tmp.sh"
  Remove-Item $scriptPath -ErrorAction SilentlyContinue
  if ($LASTEXITCODE -ne 0) { throw "WSL compile failed" }

  Write-Host "=== Done. Run with: wsl $WslBuildDir/checker [path/to/input.smt2] ==="
}
finally {
  Pop-Location
}
