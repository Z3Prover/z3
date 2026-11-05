#!/usr/bin/env python3
"""Check that the audit toolchain verifies C++ and rejects a false contract."""

import argparse
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vercors", required=True, type=Path)
    args = parser.parse_args()
    verifier = args.vercors.resolve(strict=True)
    with tempfile.TemporaryDirectory(prefix="vercors-cpp-smoke-") as directory:
        for name, result in [("valid", "x + 1"), ("invalid", "x")]:
            source = Path(directory) / f"{name}.cpp"
            source.write_text(
                "//@ requires 0 <= x && x < 100;\n"
                "//@ ensures \\result == x + 1;\n"
                f"int increment(int x) {{ return {result}; }}\n",
                encoding="utf-8",
            )
            command = [
                str(verifier), "--lang", "cpp", "--backend", "silicon",
                "--dev-total-timeout", "60", str(source),
            ]
            print("Command:", command, flush=True)
            completed = subprocess.run(
                command, cwd=directory, capture_output=True, text=True, timeout=120,
            )
            output = completed.stdout + completed.stderr
            print(output, end="", flush=True)
            print(f"{name}: exit {completed.returncode}", flush=True)
            if name == "valid":
                if completed.returncode != 0 or "Verification completed successfully." not in output:
                    raise RuntimeError("VerCors did not verify the valid C++ contract")
            elif completed.returncode != 1 or "postFailed" not in output:
                raise RuntimeError("VerCors did not reject the false C++ postcondition")


if __name__ == "__main__":
    main()
