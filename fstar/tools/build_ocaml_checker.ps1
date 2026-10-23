<#
.SYNOPSIS
  Builds the standalone, self-contained native proof-checker executable
  described in fstar/OCAML_CHECKER_REPORT.md.

.DESCRIPTION
  This pipeline runs on Windows (with WSL) or directly on Linux:

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

.PARAMETER ProfileChecker
  Instrument copied OCaml sources for per-rule/function time, allocation,
  and recursive expression-visit counts. Set Z3_FSTAR_PROFILE=1 at runtime
  to emit JSON records prefixed by "profile" on stderr. Use a separate
  WslBuildDir; instrumented timings
  include profiling overhead and are not production performance measurements.

.PARAMETER BuildJobs
  Maximum parallel C++ build jobs. On Linux the same Z3 installation is
  used for verification and native linking; WslBuildDir is a local output
  directory and Z3BuildDir is unused.
#>
param(
  [string]$FstarExe = "C:\fstar\fstar\bin\fstar.exe",
  [string]$Z3WindowsBuildDir = "",
  [string]$Z3InstallDir = "",
  [string]$OpamSwitch = "fstar53",
  [string]$WslDistribution = "",
  [string]$WslBuildDir = "~/z3checker",
  [string]$Z3BuildDir = "~/z3-native-ffi-build",
  [string]$CacheDir = "",
  [switch]$RunTests,
  [switch]$ProfileChecker,
  [ValidateRange(1, 256)]
  [int]$BuildJobs = 16
)

$ErrorActionPreference = "Continue"
$fstarDir = Split-Path -Parent $PSScriptRoot  # .../fstar
$repoDir = Split-Path -Parent $fstarDir
$originalPath = $env:PATH
$windowsHost = [Environment]::OSVersion.Platform -eq [PlatformID]::Win32NT
if (-not $Z3WindowsBuildDir) { $Z3WindowsBuildDir = Join-Path $repoDir "build" }
if (-not $Z3InstallDir) { $Z3InstallDir = Join-Path $Z3WindowsBuildDir "install" }
$Z3WindowsBuildDir = [IO.Path]::GetFullPath($Z3WindowsBuildDir)
$Z3InstallDir = [IO.Path]::GetFullPath($Z3InstallDir)
Push-Location $fstarDir
try {
  Write-Host "=== Phase 0: build and install the F*/Pulse SMT solver ==="
  $nativeOptions = @()
  if (-not $windowsHost) {
    $nativeOptions = @(
      "-DBUILD_SHARED_LIBS=OFF", "-DZ3_BUILD_OCAML_BINDINGS=ON",
      "-DZ3_BUILD_TEST_EXECUTABLES=OFF", "-DZ3_INSTALL_OCAML_BINDINGS=ON",
      "-DCMAKE_INSTALL_LIBDIR=lib", "-DZ3_OCAML_PACKAGE_INSTALLDIR=lib/ocaml/z3",
      "-DZ3_OCAML_STUB_INSTALLDIR=lib/ocaml/stublibs"
    )
  }
  & cmake -S $repoDir -B $Z3WindowsBuildDir -DCMAKE_BUILD_TYPE=Release `
      "-DCMAKE_INSTALL_PREFIX=$Z3InstallDir" -DZ3_BUILD_EXECUTABLE=ON `
      "-DCMAKE_INSTALL_PYTHON_PKG_DIR=$(Join-Path 'lib' 'python')" @nativeOptions
  if ($LASTEXITCODE -ne 0) { throw "Z3 configuration failed" }
  & cmake --build $Z3WindowsBuildDir --config Release --parallel $BuildJobs
  if ($LASTEXITCODE -ne 0) { throw "Z3 build failed" }
  & cmake --install $Z3WindowsBuildDir --config Release
  if ($LASTEXITCODE -ne 0) { throw "Z3 installation failed" }
  $binaryName = if ($windowsHost) { "z3.exe" } else { "z3" }
  $Z3Exe = Join-Path (Join-Path $Z3InstallDir "bin") $binaryName
  $env:PATH = "$(Join-Path $Z3InstallDir 'bin')$([IO.Path]::PathSeparator)$originalPath"

  if (-not $CacheDir) { $CacheDir = Join-Path $fstarDir "build_cache" }
  $extractDir = Join-Path (Join-Path $fstarDir "build_extract") "native"
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
    "Z3ValueTheory.fst", "Z3ProofTheory.fst", "Z3ProofIndex.fst", "Z3ProofSet.fst",
    "Z3ResolutionProofTheory.fst", "Z3ObservationalEquality.fst",
    "Z3BasicExprTheory.fst", "Z3BoundedBoolEquiv.fst", "Z3BooleanNormalForm.fst",
    "Z3Commutativity.fst", "Z3BooleanRewrite.fst",
    "Z3DistinctAst.fst", "Z3DistinctEmbed.fst", "Z3ArrayLemma.fst",
    "Z3ArrayRewrite.fst", "Z3Definitions.fst", "Z3ScopedModel.fst",
    "Z3LinearArithmeticTheory.fst", "Z3LinearArithmeticAst.fst", "Z3LinearArithmeticEmbed.fst",
    "Z3ArithmeticRewrite.fst", "Z3IntegerRewrite.fst", "Z3ConditionalRewrite.fst",
    "Z3NlaLemma.fst", "Z3LpCertificate.fst", "Z3LpReplay.fst", "Z3LpGomory.fst", "Z3IntegerDivision.fst",
    "Z3QuantifierNnf.fst", "Z3QuantifierVacuity.fst", "Z3QuantifierPull.fst", "Z3BinderSubstitution.fst",
    "Z3QuantifierInstantiation.fst", "Z3QuantifierReduce.fst", "Z3DestructiveEquality.fst",
    "Z3QuantifierDer.fst", "Z3Skolemization.fst",
    "Z3LambdaRewrite.fst", "Z3BvLemma.fst", "Z3BvWord.fst", "Z3BvOrder.fst", "Z3BvFresh.fst", "Z3BvFreshModel.fst", "Z3DatatypeLemma.fst",
    "Z3DatatypeValue.fst", "Z3DatatypeSignature.fst", "Z3TheoryNormalize.fst",
    "Z3UnifiedProof.fst", "Z3ProofDocument.fst", "Z3ClauseProof.fst",
    "Z3SortedSemantics.fst", "Z3SortedDatatype.fst", "Z3SortedProof.fst",
    "Z3Native.fsti", "Z3NativeProof.fst"
  )

  Write-Host "=== Phase 1a: type-check + cache ==="
  foreach ($f in $modules) {
    Write-Host "Verifying $f"
    & $FstarExe --timing --warn_error '@1..999' --cache_checked_modules --cache_dir $CacheDir --include $CacheDir --smt $Z3Exe --z3version $z3Version $f 2>&1 |
      ForEach-Object { Write-Host $_ }
    if ($LASTEXITCODE -ne 0) { throw "F* verification failed: $f" }
  }
  $missing = $modules | Where-Object { -not (Test-Path (Join-Path $CacheDir "$_.checked")) }
  if ($missing) { throw "Failed to cache: $($missing -join ', ')" }
  if ($RunTests) {
    $testModules = @(
      "Z3ResolutionProofCheckerTests.fst", "Z3ClauseProofTests.fst", "Z3NlaLemmaTests.fst", "Z3DatatypeValueTests.fst",
      "Z3SortedProofTests.fst", "Z3ScopedModelTests.fst",
      "Z3ProofJustifications.fst", "Z3PulseProofChecker.fst",
      "Z3PulseJustificationChecker.fst", "Z3LraFarkasTheory.fst",
      "Z3PulseLraChecker.fst", "Z3PulseProofCheckerTests.fst", "Z3PulseLraCheckerTests.fst"
    )
    foreach ($testModule in $testModules) {
      Write-Host "Verifying $testModule"
      & $FstarExe --timing --warn_error '@1..999' --cache_checked_modules --cache_dir $CacheDir --include $CacheDir `
          --smt $Z3Exe --z3version $z3Version $testModule
      if ($LASTEXITCODE -ne 0) { throw "F*/Pulse regressions failed: $testModule" }
    }
  }

  Write-Host "=== Phase 1b: extract to OCaml ==="
  $modNames = ($modules | Where-Object { $_ -ne "Z3Native.fsti" } |
    ForEach-Object { $_ -replace '\.fst$', '' }) -join " "
  foreach ($entry in @("Z3NativeProof.fst", "Z3NlaLemma.fst", "Z3SortedProof.fst", "Z3BvFreshModel.fst")) {
    & $FstarExe --warn_error '@1..999' --codegen OCaml --cache_dir $CacheDir --include $CacheDir --odir $extractDir `
        --smt $Z3Exe --z3version $z3Version --extract $modNames $entry
    if ($LASTEXITCODE -ne 0) { throw "OCaml extraction failed: $entry" }
  }

  Write-Host "=== Phase 2: compile native checker ==="
  if ($windowsHost) {
    $drive = $fstarDir.Substring(0, 1).ToLowerInvariant()
    $wslFstarDir = "/mnt/$drive/" + $fstarDir.Substring(3).Replace('\', '/')
  }
  else {
    $wslFstarDir = $fstarDir
    if ($WslBuildDir.StartsWith("~/")) { $WslBuildDir = Join-Path $HOME $WslBuildDir.Substring(2) }
    $WslBuildDir = [IO.Path]::GetFullPath($WslBuildDir)
  }
  $order = @(
    "prims.ml", "fStar_Pervasives.ml", "fStar_Pervasives_Native.ml", "fStar_List_Tot_Base.ml",
    "fStar_UInt.ml", "fStar_FunctionalExtensionality.ml",
    "Z3AstTheory.ml", "Z3ArrayTheory.ml", "Z3SeqTheory.ml", "Z3BvTheory.ml", "Z3ValueTheory.ml",
    "Z3ProofTheory.ml", "Z3ProofIndex.ml", "Z3ProofSet.ml",
    "Z3ResolutionProofTheory.ml", "Z3ObservationalEquality.ml",
    "Z3BasicExprTheory.ml", "Z3BoundedBoolEquiv.ml", "Z3BooleanNormalForm.ml",
    "Z3Commutativity.ml", "Z3BooleanRewrite.ml", "Z3DistinctAst.ml", "Z3DistinctEmbed.ml",
    "Z3ArrayLemma.ml", "Z3ArrayRewrite.ml",
    "Z3Definitions.ml", "Z3ScopedModel.ml", "Z3LinearArithmeticTheory.ml", "Z3LinearArithmeticAst.ml",
    "Z3LinearArithmeticEmbed.ml", "Z3ArithmeticRewrite.ml", "Z3IntegerRewrite.ml", "Z3ConditionalRewrite.ml",
    "Z3NlaLemma.ml", "Z3LpCertificate.ml", "Z3LpReplay.ml", "Z3LpGomory.ml", "Z3IntegerDivision.ml",
    "Z3QuantifierNnf.ml", "Z3QuantifierVacuity.ml", "Z3QuantifierPull.ml", "Z3BinderSubstitution.ml",
    "Z3QuantifierInstantiation.ml", "Z3QuantifierReduce.ml", "Z3DestructiveEquality.ml",
    "Z3QuantifierDer.ml", "Z3Skolemization.ml",
    "Z3LambdaRewrite.ml", "Z3BvLemma.ml", "Z3BvWord.ml", "Z3BvOrder.ml", "Z3BvFresh.ml", "Z3BvFreshModel.ml", "Z3DatatypeLemma.ml",
    "Z3DatatypeValue.ml", "Z3DatatypeSignature.ml", "Z3TheoryNormalize.ml",
    "Z3UnifiedProof.ml", "Z3ProofDocument.ml", "Z3ClauseProof.ml",
    "Z3SortedSemantics.ml", "Z3SortedDatatype.ml", "Z3SortedProof.ml",
    "Z3Native.ml", "Z3NativeProof.ml", "Z3NativeMain.ml", "main.ml"
  )
  if ($ProfileChecker) { $order = @("Z3Profile.ml") + $order }
  $orderStr = $order -join " "
  $extractedOrderStr = ($order | Where-Object {
    -not (Test-Path (Join-Path (Join-Path $fstarDir "ocaml_runtime") $_))
  }) -join " "
  $shellBuildDir = if ($WslBuildDir.StartsWith("~/")) { '$HOME/' + $WslBuildDir.Substring(2) } else { $WslBuildDir }
  $testScript = ""
  if ($RunTests) {
    $testOrder = ($order | Where-Object { $_ -ne "main.ml" }) -join " "
    $testScript = @"
cp "$wslFstarDir/tools/test_native_bridge.ml" .
ocamlfind ocamlopt -warn-error +a -package zarith,unix -linkpkg -I "`$z3_install/lib/ocaml/z3" \
  -ccopt "-L`$z3_install/lib" \
  z3ml.cmxa $testOrder test_native_bridge.ml -o native-tests
./native-tests
"@
    if ($ProfileChecker) {
      $testScript += @"

cp "$wslFstarDir/tools/test_ocaml_profile.ml" .
ocamlfind ocamlopt -warn-error +a -package unix -linkpkg \
  Z3Profile.ml test_ocaml_profile.ml -o profile-tests
Z3_FSTAR_PROFILE=1 ./profile-tests
"@
    }
  }
  $linkSetup = @"
z3_build=$Z3BuildDir
z3_install="`$z3_build/install"
cmake -S "$wslFstarDir/.." -B "`$z3_build" -DCMAKE_BUILD_TYPE=Release \
  -DBUILD_SHARED_LIBS=OFF -DZ3_BUILD_OCAML_BINDINGS=ON \
  -DZ3_BUILD_EXECUTABLE=ON -DZ3_BUILD_TEST_EXECUTABLES=OFF -DZ3_INSTALL_OCAML_BINDINGS=ON \
  -DCMAKE_INSTALL_PREFIX="`$z3_install" -DCMAKE_INSTALL_LIBDIR=lib \
  -DZ3_OCAML_PACKAGE_INSTALLDIR=lib/ocaml/z3 -DZ3_OCAML_STUB_INSTALLDIR=lib/ocaml/stublibs
cmake --build "`$z3_build" --parallel $BuildJobs
cmake --install "`$z3_build"
"@
  if (-not $windowsHost) { $linkSetup = "z3_install=`"$Z3InstallDir`"" }
  $profileScript = ""
  if ($ProfileChecker) {
    $profileScript = @"
cp "$wslFstarDir/tools/instrument_ocaml_checker.ml" extraction-tools/
(
  cd extraction-tools
  ocamlfind ocamlopt -warn-error +a -package compiler-libs.common -linkpkg \
    instrument_ocaml_checker.ml -o instrument-ocaml-checker
)
./extraction-tools/instrument-ocaml-checker $extractedOrderStr
"@
  }
  $script = @"
set -euo pipefail
export PATH="`$HOME/bin:`$PATH"
mkdir -p "$shellBuildDir"
for module in $orderStr; do
  if [ -f "$wslFstarDir/ocaml_runtime/`$module" ]; then
    cp "$wslFstarDir/ocaml_runtime/`$module" "$shellBuildDir/"
  else
    cp "$wslFstarDir/build_extract/native/`$module" "$shellBuildDir/"
  fi
done
cd "$shellBuildDir"
eval `$(opam env --switch=$OpamSwitch)
$linkSetup
"`$z3_install/bin/z3" -version
# compiler-libs' Main.cmi must not collide with the checker entry point.
mkdir -p extraction-tools
cp "$wslFstarDir/tools/complete_ocaml_projectors.ml" extraction-tools/
(
  cd extraction-tools
  ocamlfind ocamlopt -warn-error +a -package compiler-libs.common -linkpkg \
    complete_ocaml_projectors.ml -o complete-ocaml-projectors
)
./extraction-tools/complete-ocaml-projectors $extractedOrderStr
$profileScript
ocamlfind ocamlopt -warn-error +a -package zarith,unix -linkpkg -I "`$z3_install/lib/ocaml/z3" \
  -ccopt "-L`$z3_install/lib" \
  z3ml.cmxa $orderStr -o checker
$testScript
echo BUILD_OK
"@
  $scriptPath = Join-Path $extractDir "build_native_tmp.sh"
  $unixScript = $script -replace "`r`n", "`n"
  [System.IO.File]::WriteAllText($scriptPath, $unixScript, (New-Object System.Text.UTF8Encoding($false)))
  if ($windowsHost) {
    $distributionArgs = if ($WslDistribution) { @("-d", $WslDistribution) } else { @() }
    wsl @distributionArgs -e bash "$wslFstarDir/build_extract/native/build_native_tmp.sh"
  }
  else { & bash $scriptPath }
  $wslExitCode = $LASTEXITCODE
  Remove-Item $scriptPath -ErrorAction SilentlyContinue
  if ($wslExitCode -ne 0) { throw "Native build, installation, or tests failed" }
  if ($RunTests) {
    $previousChecker = $env:Z3_FSTAR_CHECKER
    $previousDistribution = $env:Z3_FSTAR_WSL_DISTRO
    try {
      $env:Z3_FSTAR_CHECKER = "$WslBuildDir/checker"
      $env:Z3_FSTAR_WSL_DISTRO = $WslDistribution
      $python = if ($windowsHost) { "python" } else { "python3" }
      & $python (Join-Path $PSScriptRoot "test_native_checker.py")
      if ($LASTEXITCODE -ne 0) { throw "Native checker CLI tests failed" }
    }
    finally {
      $env:Z3_FSTAR_CHECKER = $previousChecker
      $env:Z3_FSTAR_WSL_DISTRO = $previousDistribution
    }
  }

  $launcher = if ($windowsHost) { "wsl " } else { "" }
  Write-Host "=== Done. Run with: $launcher$WslBuildDir/checker [path/to/input.smt2] ==="
}
finally {
  $env:PATH = $originalPath
  Pop-Location
}
