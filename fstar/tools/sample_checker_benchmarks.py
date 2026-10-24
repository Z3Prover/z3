"""Sample unchanged, small UNSAT-annotated SMT-LIB inputs from pinned Zenodo archives."""

import argparse
import hashlib
import heapq
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import tarfile
import tempfile
from urllib.parse import urlsplit

import zstandard

from run_checker_regressions import file_sha256, positive_float


STATUS = re.compile(rb"\(set-info\s+:status\s+unsat\s*\)")
MAX_INPUT_BYTES = 256 * 1024


def archive_specs(document):
    if document["schema_version"] != 1:
        raise ValueError("Unsupported source manifest version")
    specs = []
    for entry in document["archives"]:
        logic = entry["logic"]
        if not re.fullmatch(r"[A-Z][A-Z0-9_]*", logic):
            raise ValueError(f"Invalid logic: {logic}")
        url = urlsplit(entry["url"])
        if (url.scheme != "https" or url.netloc != "zenodo.org" or url.query or url.fragment or
                not re.fullmatch(rf"/api/records/[0-9]+/files/{logic}\.tar\.zst/content", url.path)):
            raise ValueError(f"Expected a public Zenodo archive URL: {entry['url']}")
        if (type(entry["size_bytes"]) is not int or entry["size_bytes"] <= 0 or
                not re.fullmatch(r"[0-9a-f]{64}", entry["sha256"])):
            raise ValueError(f"Missing or invalid archive size/SHA-256: {logic}")
        sizes = document["per_logic"]
        count = sizes.get(logic) if isinstance(sizes, dict) else sizes
        if type(count) is not int or count <= 0:
            raise ValueError(f"Invalid sample size: {logic}")
        specs.append((entry, count))
    logics = [entry["logic"] for entry, _ in specs]
    if not specs or len(set(logics)) != len(logics):
        raise ValueError("Source manifest must contain distinct logic archives")
    if isinstance(document["per_logic"], dict) and set(document["per_logic"]) != set(logics):
        raise ValueError("Sample sizes must match the archive logics")
    return specs


def verify_archive(path, entry):
    if path.stat().st_size != entry["size_bytes"] or file_sha256(path) != entry["sha256"]:
        raise ValueError(f"Archive size/SHA-256 mismatch: {entry['logic']}")


def download_archive(path, entry, timeout):
    subprocess.run([
        "curl", "--fail", "--location", "--retry", "3",
        "--retry-max-time", str(timeout), "--connect-timeout", "30",
        "--max-time", str(timeout), "--silent", "--show-error",
        "--output", str(path), entry["url"],
    ], check=True, timeout=timeout + 10)


def sample_members(archive, logic, count, seed):
    eligible = 0
    seen = set()

    def candidates():
        nonlocal eligible
        for member in archive:
            # Python 3.12's streaming tar reader still retains member headers.
            archive.members.clear()
            if not member.name.endswith(".smt2"):
                continue
            name = PurePosixPath(member.name)
            if (not member.isfile() or name.is_absolute() or ".." in name.parts or
                    "\\" in member.name or ":" in member.name or
                    name.parts[:2] != ("non-incremental", logic)):
                raise ValueError(f"Unsafe or unexpected SMT-LIB archive member: {member.name}")
            relative = PurePosixPath(*name.parts[1:]).as_posix()
            if relative in seen:
                raise ValueError(f"Duplicate archive member: {member.name}")
            seen.add(relative)
            if not 0 < member.size <= MAX_INPUT_BYTES:
                continue
            with archive.extractfile(member) as source:
                content = source.read(MAX_INPUT_BYTES + 1)
            if len(content) != member.size:
                raise ValueError(f"Truncated archive member: {member.name}")
            if STATUS.search(content):
                eligible += 1
                yield relative, member.name, content

    def priority(candidate):
        relative = candidate[0]
        digest = hashlib.sha256(f"{seed}\0{logic}\0{relative}".encode("utf-8")).digest()
        return digest, relative

    selected = heapq.nsmallest(count, candidates(), key=priority)
    if eligible < count:
        raise ValueError(f"{logic}: requested {count} inputs, only {eligible} eligible")
    return sorted(selected), eligible


def sample_archive(path, entry, count, seed):
    verify_archive(path, entry)
    with path.open("rb") as compressed:
        with zstandard.ZstdDecompressor().stream_reader(compressed, read_across_frames=True) as stream:
            with tarfile.open(fileobj=stream, mode="r|") as archive:
                return sample_members(archive, entry["logic"], count, seed)


def prepare_sample(manifest, output, seed, download_timeout):
    if not seed or "\0" in seed:
        raise ValueError("Sample seed must be nonempty and contain no NUL")
    document = json.loads(manifest.read_text(encoding="utf-8"))
    specs = archive_specs(document)
    output.mkdir(parents=True, exist_ok=False)
    cases, archives = [], []
    for entry, count in specs:
        logic = entry["logic"]
        print(f"Sampling {count} {logic} inputs (seed {seed})", flush=True)
        with tempfile.TemporaryDirectory(prefix="checker-smtlib-") as directory:
            path = Path(directory) / f"{logic}.tar.zst"
            download_archive(path, entry, download_timeout)
            selected, eligible = sample_archive(path, entry, count, seed)
        archives.append({**entry, "eligible_unsat": eligible})
        for relative, member, content in selected:
            destination = output.joinpath(*PurePosixPath(relative).parts)
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(content)
            cases.append({
                "path": relative, "logic": logic, "archive_member": member,
                "sha256": hashlib.sha256(content).hexdigest(),
            })
        print(f"{logic}: selected {count} of {eligible} eligible inputs", flush=True)
    result = {
        "schema_version": 1, "source": document["source"], "seed": seed,
        "source_manifest_sha256": file_sha256(manifest),
        "per_logic": {entry["logic"]: count for entry, count in specs},
        "selection": "Lowest SHA-256(seed NUL logic NUL relative POSIX path) priorities "
                     "among regular UNSAT-annotated .smt2 files, independently per logic",
        "max_input_bytes": MAX_INPUT_BYTES,
        "archives": archives, "cases": sorted(cases, key=lambda case: case["path"]),
    }
    if "license" in document:
        result["license"] = document["license"]
    (output / "manifest.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True,
                        help="Existing cohort manifest supplying pinned archive hashes and sample sizes")
    parser.add_argument("--output", type=Path, required=True, help="New directory for inputs and manifest")
    parser.add_argument("--seed", required=True, help="Recorded seed; workflow defaults to its run ID")
    parser.add_argument("--download-timeout-seconds", type=positive_float, default=600)
    args = parser.parse_args()
    prepare_sample(args.manifest, args.output, args.seed, args.download_timeout_seconds)


if __name__ == "__main__":
    main()
