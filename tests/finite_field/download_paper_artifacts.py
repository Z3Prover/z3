#!/usr/bin/env python3
"""Download the three paper corpora without installing their Docker images.

CAV archives: retrieve ZIP directory and complete benchmark regions, validate
each extracted member's CRC, then record SHA256 per input. FMCAD: benchmarks
are inside Docker layers, so retrieve and verify the full published archive.
"""
import argparse
import json
import subprocess
import sys
import urllib.request
from pathlib import Path


ARTIFACTS = {
    'cav23': ('7865471', 'cav23-artifact-ff-init.zip', 997117354,
              [(956421623, 997117353)]),
    'cav24': ('10917330', 'cav24-artifact-ff-split-gb.zip', 2013254587,
              [(1995368293, 2013254586)]),
    'fmcad26': ('20133205', 'artifact.zip', 4642552269, None),
}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cache', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    args.cache.mkdir(parents=True, exist_ok=True)
    paths = {}
    for label, (record, key, size, ranges) in ARTIFACTS.items():
        url = 'https://zenodo.org/api/records/'+record
        with urllib.request.urlopen(url, timeout=60) as response: metadata = json.load(response)
        (args.cache/(label+'-metadata.json')).write_text(json.dumps(metadata, indent=2)+'\n')
        entry = next(f for f in metadata['files'] if f['key'] == key)
        assert entry['size'] == size
        path = args.cache/(label+'.zip'); paths[label] = path
        marker = args.cache/(label+'.download-complete')
        if not marker.exists():
            with path.open('wb') as output:
                output.truncate(size)
                for start, end in ranges or [(0, size-1)]:
                    request = urllib.request.Request(entry['links']['self'], headers={'Range': f'bytes={start}-{end}'})
                    with urllib.request.urlopen(request, timeout=120) as response:
                        assert response.status == 206
                        assert response.headers['Content-Range'] == f'bytes {start}-{end}/{size}'
                        output.seek(start); count = 0
                        while True:
                            data = response.read(4*1024*1024)
                            if not data: break
                            output.write(data); count += len(data)
                        assert count == end-start+1
            marker.write_text('Downloaded exact requested byte ranges.\n')
        print(label, path, flush=True)
    here = Path(__file__).resolve().parent
    fmcad = args.cache/'fmcad26-inputs'
    subprocess.run([sys.executable, str(here/'extract_ffproofs.py'), str(paths['fmcad26']), str(fmcad)], check=True)
    subprocess.run([sys.executable, str(here/'artifact_corpus.py'), '--cav23', str(paths['cav23']),
                    '--cav24', str(paths['cav24']), '--fmcad26', str(fmcad), '--out', str(args.out)], check=True)


if __name__ == '__main__': main()
