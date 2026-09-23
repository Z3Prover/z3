#!/usr/bin/env python3
"""Read the published Docker archive as data; extract only experiment inputs.

No Docker daemon, artifact executable, image installation or archive-wide
extraction is used. Nested layers are streamed to keep disk usage bounded.
"""
import argparse
import hashlib
import json
import tarfile
import zipfile
from pathlib import Path, PurePosixPath


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('archive', type=Path)
    ap.add_argument('out', type=Path)
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    hasher = hashlib.sha256()
    with args.archive.open('rb') as source:
        for chunk in iter(lambda: source.read(8*1024*1024), b''): hasher.update(chunk)
    digest = hasher.hexdigest()
    assert digest == '8ab6cfd71baf3be2ce163c564565a0cbe31349c1364558b77e98cddfd03a6cb8', digest
    captured = []
    with zipfile.ZipFile(args.archive) as z:
        with z.open('artifact/artifact-ffproofs-v1.tar.gz') as image:
            with tarfile.open(fileobj=image, mode='r|gz') as outer:
                for entry in outer:
                    if not entry.isfile() or entry.size < 512: continue
                    if not (entry.name.endswith('/layer.tar') or entry.name.startswith('blobs/sha256/')): continue
                    print('reading layer', entry.name, entry.size, flush=True)
                    stream = outer.extractfile(entry)
                    try:
                        with tarfile.open(fileobj=stream, mode='r|*') as layer:
                            for item in layer:
                                marker = 'home/user/artifact-ffproofs/'
                                name = item.name.removeprefix('./')
                                if not item.isfile() or not name.startswith(marker): continue
                                relative = name[len(marker):]
                                p = PurePosixPath(relative)
                                if '..' in p.parts or p.is_absolute(): raise ValueError(relative)
                                wanted = relative.startswith('benchmarks/SMT-LIB/') or (
                                    '/' not in relative and (relative.startswith('benchmark_set') or relative.endswith(('.md','.py','.sh'))))
                                if not wanted: continue
                                target = args.out/relative; target.parent.mkdir(parents=True, exist_ok=True)
                                target.write_bytes(layer.extractfile(item).read())
                                captured.append(relative)
                    except tarfile.ReadError:
                        # OCI configuration JSONs share the blob directory.
                        if entry.size > 1048576: raise
            # Consume the ZIP member to verify its stored CRC too.
            while image.read(1048576): pass
    (args.out/'extraction.json').write_text(json.dumps(dict(archive_sha256=digest, files=captured), indent=2)+'\n')
    # The immutable published image stores each selected input exactly once.
    # Reject an unexpected layered overwrite instead of guessing OCI layer order.
    assert len(captured) == len(set(captured)), 'selected files occur in multiple layers'
    print('captured', len(captured), 'files;', len(list(args.out.rglob('*.smt2'))), 'SMT2 inputs')


if __name__ == '__main__': main()
