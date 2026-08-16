"""Fetch a small, explicitly-listed public benchmark subset.

The official MaxSAT Evaluation links are retained in ``PUBLIC_SPECS`` for
provenance.  Their archives are intentionally skipped by the 5 MiB transfer
cap; individual, small examples from the MIT-licensed DPMaxSAT repository and
the Z3 repository are downloaded instead.  No crawling or unbounded archive
extraction is performed.
"""
from __future__ import annotations

import argparse
import json
import os
import re
from pathlib import Path
import time
import urllib.error
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parent
PUBLIC = ROOT / "public"
SOURCES_FILE = PUBLIC / "SOURCES.json"
DEFAULT_MAX_BYTES = 5 * 1024 * 1024
DEFAULT_TIMEOUT = 15.0
USER_AGENT = "parallel-maxsmt-benchmark-fetch/1.0"

# Every URL is deliberately spelled out.  The first two are the official MSE
# 2023 anytime tracks (the archive sizes are checked and skipped).  The
# individual entries are small files from public solver/example repositories;
# no crawler or archive extraction is used.
PUBLIC_SPECS = [
    {
        "url": "https://www.cs.helsinki.fi/group/coreo/MSE2023-anytime-instances/MSE2023-anytime-W-benchmarks.zip",
        "filename": "mse2023_anytime_weighted.zip",
        "family": "maxsat-evaluation-2023-anytime-weighted-archive",
        "format": "archive",
    },
    {
        "url": "https://www.cs.helsinki.fi/group/coreo/MSE2023-anytime-instances/MSE2023-anytime-UW-benchmarks.zip",
        "filename": "mse2023_anytime_unweighted.zip",
        "family": "maxsat-evaluation-2023-anytime-unweighted-archive",
        "format": "archive",
    },
    {
        "url": "https://raw.githubusercontent.com/zzwonder/DPMaxSAT/main/examples/cat.wcnf",
        "filename": "dpmaxsat_cat.wcnf",
        "family": "DPMaxSAT-CATS",
        "format": "wcnf",
    },
    {
        "url": "https://raw.githubusercontent.com/zzwonder/DPMaxSAT/main/dmc/test.cnf",
        "filename": "dpmaxsat_test.cnf",
        "family": "DPMaxSAT-demo-CNF",
        "format": "cnf",
    },
    {
        "url": "https://raw.githubusercontent.com/Z3Prover/z3/master/examples/maxsat/ex.smt",
        "filename": "z3_maxsat_ex.smt",
        "family": "Z3-MaxSAT-example",
        "format": "smt2",
    },
    {
        "url": "https://raw.githubusercontent.com/tobipaxe/PacoseMaxSATSolver/main/MaxSATRegressionSuite/baseWCNFs/smallo0.wcnf",
        "filename": "pacose_smallo0.wcnf",
        "family": "Pacose-regression-unweighted",
        "format": "wcnf",
        "weighted": False,
        "license": "MIT (Pacose repository)",
    },
    {
        "url": "https://raw.githubusercontent.com/tobipaxe/PacoseMaxSATSolver/main/MaxSATRegressionSuite/baseWCNFs/smallo1.wcnf",
        "filename": "pacose_smallo1.wcnf",
        "family": "Pacose-regression-unweighted",
        "format": "wcnf",
        "weighted": False,
        "license": "MIT (Pacose repository)",
    },
    {
        "url": "https://raw.githubusercontent.com/tobipaxe/PacoseMaxSATSolver/main/MaxSATRegressionSuite/baseWCNFs/TwoMinimalContradictingSoftClauses.wcnf",
        "filename": "pacose_two_minimal_contradicting.wcnf",
        "family": "Pacose-regression-unweighted",
        "format": "wcnf",
        "weighted": False,
        "license": "MIT (Pacose repository)",
    },
    {
        "url": "https://raw.githubusercontent.com/maxbannach/i2hs/main/examples/planning_wt-depot01c.wcsp.dir.wcnf",
        "filename": "i2hs_planning_depot01c.wcnf",
        "family": "i2hs-planning-weighted",
        "format": "wcnf",
        "weighted": True,
        "license": "MIT (i2hs repository)",
    },
    {
        "url": "https://raw.githubusercontent.com/maxbannach/i2hs/main/examples/planning_wt-driverlog01bc.wcsp.dir.wcnf",
        "filename": "i2hs_planning_driverlog01bc.wcnf",
        "family": "i2hs-planning-weighted",
        "format": "wcnf",
        "weighted": True,
        "license": "MIT (i2hs repository)",
    },
    {
        "url": "https://raw.githubusercontent.com/maxbannach/i2hs/main/examples/qcp_wt-file_qc_wcnf_N10_H60_2.wcnf",
        "filename": "i2hs_qcp_N10_H60_2.wcnf",
        "family": "i2hs-qcp-weighted",
        "format": "wcnf",
        "weighted": True,
        "license": "MIT (i2hs repository)",
    },
 ]


def _request(url: str, method: str = "HEAD", timeout: float = DEFAULT_TIMEOUT):
    request = urllib.request.Request(url, method=method, headers={"User-Agent": USER_AGENT})
    return urllib.request.urlopen(request, timeout=timeout)


def _content_is_valid(data: bytes, spec: dict) -> tuple[bool, str]:
    fmt = spec["format"]
    if fmt == "archive":
        if data[:4] not in {b"PK\x03\x04", b"PK\x05\x06", b"PK\x07\x08"}:
            return False, "response is not a ZIP archive"
        return True, "ZIP header verified"
    try:
        text = data.decode("utf-8", "strict")
    except UnicodeDecodeError:
        return False, "response is not UTF-8 text"
    if fmt == "wcnf":
        # Both pre-2022 ``p wcnf`` and the newer headerless ``h`` format are
        # used by public MaxSAT repositories.
        has_header = "p wcnf" in text.lower()
        has_new_clause = re.search(r"(?m)^\s*h(?:\s|$)", text) or re.search(r"(?m)^\s*\d+\s+.*\s0\s*$", text)
        if not (has_header or has_new_clause):
            return False, "response lacks a recognizable WCNF clause/header"
    if fmt == "cnf" and "p cnf" not in text.lower():
        return False, "response lacks a p cnf header"
    if fmt == "smt2" and "assert-soft" not in text:
        return False, "response lacks assert-soft"
    return True, "text format marker verified"


def _probe(spec: dict, timeout: float) -> tuple[int, int | None, str]:
    """Probe one URL without writing; return (status, size, note)."""
    try:
        with _request(spec["url"], "HEAD", timeout) as response:
            status = int(response.status)
            size_header = response.headers.get("Content-Length")
            size = int(size_header) if size_header and size_header.isdigit() else None
            return status, size, response.headers.get("Content-Type", "")
    except urllib.error.HTTPError as exc:
        return int(exc.code), None, str(exc.reason)
    except (urllib.error.URLError, TimeoutError, OSError) as exc:
        raise RuntimeError(f"network/host unavailable: {exc}") from exc


def _validate_zip_size(path: Path, max_bytes: int) -> tuple[bool, str]:
    try:
        with zipfile.ZipFile(path) as archive:
            total = sum(info.file_size for info in archive.infolist())
    except (zipfile.BadZipFile, OSError) as exc:
        return False, f"invalid ZIP content: {exc}"
    if total > max_bytes:
        return False, f"uncompressed ZIP contents {total} bytes exceed cap {max_bytes}"
    return True, f"ZIP uncompressed bytes={total}"


def _download(spec: dict, timeout: float, max_bytes: int) -> tuple[str, int | None, str]:
    PUBLIC.mkdir(parents=True, exist_ok=True)
    destination = PUBLIC / spec["filename"]
    if destination.exists():
        data = destination.read_bytes()
        valid, note = _content_is_valid(data[:16384], spec)
        if valid and spec["format"] == "archive":
            valid, note = _validate_zip_size(destination, max_bytes)
        if valid:
            return "existing", len(data), note
        return "failure", len(data), f"existing file is invalid: {note}"

    temporary = destination.with_suffix(destination.suffix + ".part")
    try:
        with _request(spec["url"], "GET", timeout) as response:
            status = int(response.status)
            if status != 200:
                return "failure", None, f"HTTP status {status}, expected 200"
            length_header = response.headers.get("Content-Length")
            advertised = int(length_header) if length_header and length_header.isdigit() else None
            # Read a small prefix before rejecting a huge archive so the run
            # still verifies that the successful response has valid content.
            prefix = response.read(16384)
            valid, note = _content_is_valid(prefix, spec)
            if not valid:
                return "failure", advertised, note
            if advertised is not None and advertised > max_bytes:
                return "oversize", advertised, f"advertised size {advertised} exceeds cap {max_bytes}"
            written = len(prefix)
            with temporary.open("wb") as output:
                output.write(prefix)
                while True:
                    if written > max_bytes:
                        return "oversize", written, f"download exceeded cap {max_bytes}"
                    chunk = response.read(min(64 * 1024, max_bytes + 1 - written))
                    if not chunk:
                        break
                    output.write(chunk)
                    written += len(chunk)
                    if written > max_bytes:
                        return "oversize", written, f"download exceeded cap {max_bytes}"
        if spec["format"] == "archive":
            valid, note = _validate_zip_size(temporary, max_bytes)
            if not valid:
                return "oversize" if "exceed cap" in note else "failure", written, note
        else:
            data = temporary.read_bytes()
            valid, note = _content_is_valid(data, spec)
            if not valid:
                return "failure", written, note
        os.replace(temporary, destination)
        return "downloaded", written, note
    except (urllib.error.HTTPError, urllib.error.URLError, TimeoutError, OSError) as exc:
        return "failure", None, f"network/host unavailable or I/O error: {exc}"
    finally:
        try:
            temporary.unlink()
        except OSError:
            pass


def fetch(*, dry_run: bool = False, timeout: float = DEFAULT_TIMEOUT, max_bytes: int = DEFAULT_MAX_BYTES) -> int:
    records: list[dict] = []
    failures = 0
    prior_by_url: dict[str, dict] = {}
    if SOURCES_FILE.exists():
        try:
            prior = json.loads(SOURCES_FILE.read_text(encoding="utf-8"))
            prior_by_url = {str(item.get("url")): item for item in prior if isinstance(item, dict)}
        except (OSError, json.JSONDecodeError):
            prior_by_url = {}
    print(f"benchmark fetch: {len(PUBLIC_SPECS)} explicit public URLs")
    print(f"size cap: {max_bytes} bytes ({max_bytes / 1024 / 1024:.2f} MiB), timeout: {timeout:g}s")
    for spec in PUBLIC_SPECS:
        print(f"URL {spec['url']}")
        record = {
            "url": spec["url"],
            "path": f"public/{spec['filename']}",
            "family": spec["family"],
            "format": spec["format"],
        }
        if "weighted" in spec:
            record["weighted"] = bool(spec["weighted"])
        if "license" in spec:
            record["license"] = spec["license"]
        if dry_run:
            try:
                status, size, content_type = _probe(spec, timeout)
                if status != 200:
                    failures += 1
                    print(f"  ERROR HTTP {status} (expected 200): {content_type}")
                    record.update(status="failure", http_status=status, note=content_type)
                elif size is not None and size > max_bytes:
                    print(f"  HTTP 200; {size} bytes; DRY-RUN SKIP over cap")
                    record.update(status="oversize", http_status=status, size_bytes=size, note="over cap")
                else:
                    print(f"  HTTP 200; {size if size is not None else 'unknown'} bytes; DRY-RUN would download")
                    record.update(status="would-download", http_status=status, size_bytes=size)
            except RuntimeError as exc:
                failures += 1
                print(f"  ERROR {exc}")
                record.update(status="failure", note=str(exc))
            records.append(record)
            continue

        status, size, note = _download(spec, timeout, max_bytes)
        if status == "failure":
            failures += 1
            print(f"  ERROR {note}")
        elif status == "oversize":
            print(f"  HTTP 200; SKIP {note}")
        else:
            print(f"  {status.upper()} {size} bytes; {note}")
        record.update(status=status, size_bytes=size, note=note)
        previous = prior_by_url.get(spec["url"], {})
        if status == "downloaded":
            record["first_status"] = "downloaded"
        elif status == "existing":
            record["first_status"] = previous.get("first_status", previous.get("status", "existing"))
        records.append(record)

    if not dry_run:
        PUBLIC.mkdir(parents=True, exist_ok=True)
        SOURCES_FILE.write_text(json.dumps(records, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"wrote source receipt: {SOURCES_FILE}")
    print("manifest of fetch attempt:")
    print(json.dumps(records, indent=2, sort_keys=True))
    if failures:
        print(f"ERROR: {failures} URL(s) failed; network/host failure or invalid response", flush=True)
        return 2
    print("fetch completed without URL failures")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dry-run", action="store_true", help="probe URLs and print actions without writing files")
    parser.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT, help="per-socket timeout in seconds")
    parser.add_argument("--max-mb", type=float, default=5.0, help="maximum downloaded/uncompressed size in MiB")
    args = parser.parse_args()
    if args.timeout <= 0 or args.max_mb <= 0:
        parser.error("--timeout and --max-mb must be positive")
    return fetch(dry_run=args.dry_run, timeout=args.timeout, max_bytes=int(args.max_mb * 1024 * 1024))


if __name__ == "__main__":
    raise SystemExit(main())
