<#
.SYNOPSIS
  Builds the standalone, self-contained native proof-checker executable
  described in fstar/OCAML_CHECKER_REPORT.md.

.DESCRIPTION
  This pipeline first builds and installs the Windows SMT solver:

    Phase 0 (Windows, CMake): build Z3 from this checkout and install it
    under build\install. Every F*/Pulse invocation selects that installed
    executable explicitly, including verification, extraction, and tests.

    Phase 1 (Windows, fstar.exe): type-check the shared typed checker,
    and direct native marshaler, caching a `.checked` file per module
    (fstar.exe's OCaml-extraction backend requires every module --
    including the one being extracted, not just its dependencies -- to
    already have a `.checked` file on disk, so this is done bottom-up,
    one module at a time). Then re-invoke
    fstar.exe with `--codegen OCaml` against those caches to produce a
    plain `.ml` file per module under `--odir`.

    Phase 2 (WSL, CMake + ocamlfind ocamlopt): build and install static libz3 and
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
    - fstar.exe, CMake, and a Windows C++20 compiler environment.
    - WSL with an opam switch named 'fstar53' using OCaml 5.3.0 (the
      OCaml release whose `.cmi` magic number matches this F*
      distribution's own build -- see the report for how this was
      determined), Zarith, CMake, Python 3 for Z3's build-time code
      generation, and a C++20 compiler.

.PARAMETER WslBuildDir
  Where to copy the built executable *inside WSL* (default:
  ~/z3checker/checker). Printed at the end as a `wsl <path>` command.

.PARAMETER Z3WindowsBuildDir
  Windows CMake build directory for the F*/Pulse SMT solver (default: build).

.PARAMETER Z3InstallDir
  Windows installation prefix (default: build\install). Verification and
  extraction use bin\z3.exe from this installation, never a system solver.

.PARAMETER CacheDir
  Optional existing F* cache directory. Modules are still checked for
  source/dependency changes before extraction.

.PARAMETER Z3BuildDir
  WSL CMake build directory for the static Z3 library and official OCaml bindings.
  They are installed under this directory's install subdirectory before linking.

.PARAMETER RunTests
  Verify F*/Pulse regressions and execute native bridge and CLI tests.
#>
param(
  [string]$FstarExe = "C:\fstar\fstar\bin\fstar.exe",
  [string]$Z3WindowsBuildDir = "",
  [string]$Z3InstallDir = "",
  [string]$OpamSwitch = "fstar53",
  [string]$WslBuildDir = "~/z3checker",
  [string]$Z3BuildDir = "~/z3-native-ffi-build",
  [string]$CacheDir = "",
  [switch]$RunTests
)

$ErrorActionPreference = "Continue"
$fstarDir = Split-Path -Parent $PSScriptRoot  # .../fstar
$repoDir = Split-Path -Parent $fstarDir
$originalPath = $env:PATH
if (-not $Z3WindowsBuildDir) { $Z3WindowsBuildDir = Join-Path $repoDir "build" }
if (-not $Z3InstallDir) { $Z3InstallDir = Join-Path $Z3WindowsBuildDir "install" }
$Z3WindowsBuildDir = [IO.Path]::GetFullPath($Z3WindowsBuildDir)
$Z3InstallDir = [IO.Path]::GetFullPath($Z3InstallDir)
Push-Location $fstarDir
try {
  Write-Host "=== Phase 0: build and install the F*/Pulse SMT solver ==="
  & cmake -S $repoDir -B $Z3WindowsBuildDir -DCMAKE_BUILD_TYPE=Release `
      "-DCMAKE_INSTALL_PREFIX=$Z3InstallDir" -DZ3_BUILD_EXECUTABLE=ON `
      "-DCMAKE_INSTALL_PYTHON_PKG_DIR=lib\python"
  if ($LASTEXITCODE -ne 0) { throw "Windows Z3 configuration failed" }
  & cmake --build $Z3WindowsBuildDir --config Release --parallel 16
  if ($LASTEXITCODE -ne 0) { throw "Windows Z3 build failed" }
  & cmake --install $Z3WindowsBuildDir --config Release
  if ($LASTEXITCODE -ne 0) { throw "Windows Z3 installation failed" }
  $Z3Exe = Join-Path $Z3InstallDir "bin\z3.exe"
  $env:PATH = "$(Join-Path $Z3InstallDir 'bin');$originalPath"

  if (-not $CacheDir) { $CacheDir = Join-Path $fstarDir "build_cache" }
  $extractDir = Join-Path $fstarDir "build_extract\native"
  New-Item -ItemType Directory -Force -Path $CacheDir | Out-Null
  New-Item -ItemType Directory -Force -Path $extractDir | Out-Null

  $versionOutput = & $Z3Exe -version 2>&1
  $versionMatch = [regex]::Match(($versionOutput -join "`n"), '\bZ3 version ([0-9]+\.[0-9]+\.[0-9]+)\b')
  if ($LASTEXITCODE -ne 0 -or -not $versionMatch.Success) {
    throw "Cannot determine F* SMT solver version from '$Z3Exe': $versionOutput"
  }
  $z3Version = $versionMatch.Groups[1].Value
  Write-Host "Installed F*/Pulse SMT solver: $Z3Exe ($versionOutput)"

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
    "Z3ArithmeticRewrite.fst",
    "Z3NlaLemma.fst",
    "Z3UnifiedProof.fst", "Z3ProofDocument.fst",
    "Z3Native.fsti", "Z3NativeProof.fst"
  )

  Write-Host "=== Phase 1a: type-check + cache ==="
  foreach ($f in $modules) {
    & $FstarExe --cache_checked_modules --cache_dir $CacheDir --include $CacheDir --smt $Z3Exe --z3version $z3Version $f 2>&1 |
      ForEach-Object { Write-Host $_ }
    if ($LASTEXITCODE -ne 0) { throw "F* verification failed: $f" }
  }
  $missing = $modules | Where-Object { -not (Test-Path (Join-Path $CacheDir "$_.checked")) }
  if ($missing) { throw "Failed to cache: $($missing -join ', ')" }
  if ($RunTests) {
    $testModules = @(
      "Z3ResolutionProofCheckerTests.fst", "Z3NlaLemmaTests.fst",
      "Z3ProofJustifications.fst", "Z3PulseProofChecker.fst",
      "Z3PulseJustificationChecker.fst", "Z3LraFarkasTheory.fst",
      "Z3PulseLraChecker.fst", "Z3PulseProofCheckerTests.fst", "Z3PulseLraCheckerTests.fst"
    )
    foreach ($testModule in $testModules) {
      & $FstarExe --cache_checked_modules --cache_dir $CacheDir --include $CacheDir `
          --smt $Z3Exe --z3version $z3Version $testModule
      if ($LASTEXITCODE -ne 0) { throw "F*/Pulse regressions failed: $testModule" }
    }
  }

  Write-Host "=== Phase 1b: extract to OCaml ==="
  $modNames = ($modules | Where-Object { $_ -ne "Z3Native.fsti" } |
    ForEach-Object { $_ -replace '\.fst$', '' }) -join " "
  foreach ($entry in @("Z3NativeProof.fst", "Z3NlaLemma.fst")) {
    & $FstarExe --codegen OCaml --cache_dir $CacheDir --include $CacheDir --odir $extractDir `
        --smt $Z3Exe --z3version $z3Version --extract $modNames $entry
    if ($LASTEXITCODE -ne 0) { throw "OCaml extraction failed: $entry" }
  }

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
    "Z3LinearArithmeticEmbed.ml", "Z3ArithmeticRewrite.ml", "Z3NlaLemma.ml", "Z3UnifiedProof.ml", "Z3ProofDocument.ml",
    "Z3Native.ml", "Z3NativeProof.ml", "Z3NativeMain.ml", "main.ml"
  )
  $orderStr = $order -join " "
  $testScript = ""
  if ($RunTests) {
    $testOrder = ($order | Where-Object { $_ -ne "main.ml" -and $_ -ne "Z3NativeMain.ml" }) -join " "
    $testScript = @"
cp "$wslFstarDir/tools/test_native_bridge.ml" .
ocamlfind ocamlopt -package zarith,unix -linkpkg -I "`$z3_install/lib/ocaml/z3" \
  -ccopt "-L`$z3_install/lib" \
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
z3_install="`$z3_build/install"
cmake -S "$wslFstarDir/.." -B "`$z3_build" -DCMAKE_BUILD_TYPE=Release \
  -DBUILD_SHARED_LIBS=OFF -DZ3_BUILD_OCAML_BINDINGS=ON \
  -DZ3_BUILD_EXECUTABLE=ON -DZ3_BUILD_TEST_EXECUTABLES=OFF -DZ3_INSTALL_OCAML_BINDINGS=ON \
  -DCMAKE_INSTALL_PREFIX="`$z3_install" -DCMAKE_INSTALL_LIBDIR=lib \
  -DZ3_OCAML_PACKAGE_INSTALLDIR=lib/ocaml/z3 -DZ3_OCAML_STUB_INSTALLDIR=lib/ocaml/stublibs
cmake --build "`$z3_build" --parallel 16
cmake --install "`$z3_build"
"`$z3_install/bin/z3" -version
ocamlfind ocamlopt -package zarith,unix -linkpkg -I "`$z3_install/lib/ocaml/z3" \
  -ccopt "-L`$z3_install/lib" \
  z3ml.cmxa $orderStr -o checker
$testScript
echo BUILD_OK
"@
  $scriptPath = Join-Path $fstarDir "build_wsl_tmp.sh"
  $unixScript = $script -replace "`r`n", "`n"
  [System.IO.File]::WriteAllText($scriptPath, $unixScript, (New-Object System.Text.UTF8Encoding($false)))
  wsl -e bash "$wslFstarDir/build_wsl_tmp.sh"
  $wslExitCode = $LASTEXITCODE
  Remove-Item $scriptPath -ErrorAction SilentlyContinue
  if ($wslExitCode -ne 0) { throw "WSL build, installation, or native tests failed" }
  if ($RunTests) {
    $previousChecker = $env:Z3_FSTAR_CHECKER
    try {
      $env:Z3_FSTAR_CHECKER = "$WslBuildDir/checker"
      & python (Join-Path $PSScriptRoot "test_native_checker.py")
      if ($LASTEXITCODE -ne 0) { throw "Native checker CLI tests failed" }
    }
    finally {
      $env:Z3_FSTAR_CHECKER = $previousChecker
    }
  }

  Write-Host "=== Done. Run with: wsl $WslBuildDir/checker [path/to/input.smt2] ==="
}
finally {
  $env:PATH = $originalPath
  Pop-Location
}
