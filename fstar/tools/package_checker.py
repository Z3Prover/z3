"""Package a native checker as an executable-preserving, smoke-tested tarball."""

import argparse
import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import tarfile
import tempfile


ROOT = Path(__file__).resolve().parents[2]


def package(args):
    checker = args.checker.resolve()
    with checker.open("rb") as binary:
        if binary.read(4) != b"\x7fELF":
            raise ValueError(f"Expected a Linux ELF executable: {checker}")
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    name = f"pulse-checker-{args.backend}-linux-{platform.machine()}"
    archive = output / f"{name}.tar.gz"
    licenses = [ROOT / "LICENSE.txt", args.fstar.resolve().parent.parent / "LICENSE"]
    licenses += args.extra_license
    metadata = {
        "backend": args.backend,
        "system": platform.platform(),
        "commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "fstar": subprocess.check_output([str(args.fstar), "--version"], text=True).strip(),
        "sha256": hashlib.sha256(checker.read_bytes()).hexdigest(),
        "libraries": subprocess.check_output(["ldd", str(checker)], text=True),
    }
    if "not found" in metadata["libraries"]:
        raise RuntimeError("Checker has unresolved shared libraries:\n" + metadata["libraries"])
    with tempfile.TemporaryDirectory(prefix="checker-package-") as temporary:
        directory = Path(temporary) / name
        directory.mkdir()
        executable = directory / "checker"
        shutil.copy2(checker, executable)
        executable.chmod(0o755)
        for index, source in enumerate(licenses):
            shutil.copyfile(source, directory / f"LICENSE-{index}-{source.name}")
        (directory / "build.json").write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
        (directory / "README.txt").write_text(
            f"Z3 proof checker ({args.backend}), built on Linux {platform.machine()}.\n"
            "Run: ./checker [--stats] [--diagnostics] [input.smt2]\n"
            "Incremental input: ./checker --interactive\n"
            "Only ACCEPT certifies UNSAT. PARTIAL n retains n unchecked obligations.\n"
            "Exit codes: ACCEPT=0 REJECT=1 ERROR=2 PARTIAL=3 SAT=4 UNKNOWN=5.\n"
            "No build-time F*, opam, OCaml installation, or external z3 executable is needed.\n"
            "Requires glibc and libstdc++; the OCaml binary also requires libgmp.so.10.\n"
            "See build.json for the runner, source revision, and shared-library dependencies.\n",
            encoding="utf-8",
        )
        smoke = subprocess.run(
            [str(executable)], input="(assert false)", capture_output=True, text=True,
            env={"PATH": "/usr/bin:/bin", "LC_ALL": "C.UTF-8"}, timeout=30,
        )
        if (smoke.returncode, smoke.stdout.strip()) != (0, "ACCEPT"):
            raise RuntimeError(f"Packaged checker failed the clean-environment smoke check: {smoke}")
        def permissions(member):
            member.mode = 0o755 if member.isdir() or member.name == f"{name}/checker" else 0o644
            return member
        with tarfile.open(archive, "w:gz") as tar:
            tar.add(directory, arcname=name, filter=permissions)
    digest = hashlib.sha256(archive.read_bytes()).hexdigest()
    archive.with_suffix(archive.suffix + ".sha256").write_text(
        f"{digest}  {archive.name}\n", encoding="ascii"
    )
    print(archive)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checker", type=Path, required=True)
    parser.add_argument("--backend", choices=("ocaml", "cherry"), required=True)
    parser.add_argument("--fstar", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--extra-license", type=Path, action="append", default=[])
    args = parser.parse_args()
    try:
        package(args)
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        parser.exit(1, f"ERROR {error}\n")


if __name__ == "__main__":
    main()
