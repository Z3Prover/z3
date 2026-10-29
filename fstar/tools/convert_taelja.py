"""Convert an accepted native checker proof into a Taelja TPTP derivation."""

import argparse
import math
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def run(command, timeout):
    try:
        return subprocess.run(command, check=True, capture_output=True,
                              text=True, encoding="utf-8", timeout=timeout)
    except subprocess.CalledProcessError as error:
        detail = "\n".join(part.strip() for part in (error.stdout, error.stderr) if part)
        raise RuntimeError(
            f"{command[0]} exited with status {error.returncode}: {detail}") from error
    except subprocess.TimeoutExpired as error:
        raise RuntimeError(f"{command[0]} exceeded the {timeout:g}s timeout") from error
    except OSError as error:
        raise RuntimeError(f"Cannot execute {command[0]}: {error}") from error


def convert(source, output, checker, taelja, timeout=60):
    source, output = Path(source).resolve(), Path(output).resolve()
    if source == output:
        raise ValueError("The output must not overwrite the SMT-LIB input")
    if not math.isfinite(timeout) or timeout <= 0:
        raise ValueError("The timeout must be a finite positive number")
    with tempfile.TemporaryDirectory(prefix="z3-taelja-") as temporary:
        proof = Path(temporary) / "proof.tstp"
        checked = run([str(checker), "--tstp-out", str(proof), str(source)], timeout)
        if checked.stdout.strip() != "ACCEPT":
            raise RuntimeError(f"Native checker did not accept the proof: {checked.stdout.strip()}")
        if not proof.is_file() or proof.stat().st_size == 0:
            raise RuntimeError("Native checker did not produce a TSTP refutation")
        translated = run([str(taelja), "--tptp", str(proof)], timeout)
        if not translated.stdout.strip():
            raise RuntimeError("Taelja produced an empty derivation")
        with tempfile.TemporaryDirectory(prefix=".taelja-", dir=output.parent) as staging:
            pending = Path(staging) / "proof.p"
            pending.write_text(translated.stdout, encoding="utf-8", newline="\n")
            os.replace(pending, output)
        if checked.stderr:
            print(checked.stderr, end="", file=sys.stderr)
        if translated.stderr:
            print(translated.stderr, end="", file=sys.stderr)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="SMT-LIB input for the native checker")
    parser.add_argument("--output", type=Path, required=True, help="Destination TPTP derivation")
    parser.add_argument("--checker", default="checker", help="Native checker executable")
    parser.add_argument("--taelja", default="taelja", help="Taelja executable")
    parser.add_argument("--timeout", type=float, default=60, help="Wall timeout per process in seconds")
    args = parser.parse_args()
    try:
        convert(args.input, args.output, args.checker, args.taelja, args.timeout)
    except (RuntimeError, ValueError, OSError) as error:
        parser.exit(2, f"ERROR {error}\n")
    print(f"ACCEPT; Taelja TPTP derivation written to {args.output}", file=sys.stderr)


if __name__ == "__main__":
    main()
