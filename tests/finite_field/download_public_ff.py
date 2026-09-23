#!/usr/bin/env python3
"""Retrieve a predetermined 54-case, 255-bit CAV'23 ZK compiler benchmark slice.

Only the ZIP index and benchmark data region are downloaded, not its Docker image.
ZIP CRCs are checked during extraction. The manifest records every input SHA-256.
"""
import argparse
import hashlib
import itertools
import json
import tempfile
import urllib.request
import zipfile
from pathlib import Path

URL = 'https://zenodo.org/records/7864537/files/cav23-artifact-ff-init.zip?download=1'
SIZE = 997117354
RANGES = [(996357873, 997117353), (956657957, 996342427)]


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--archive',type=Path,help='use a local archive instead of downloading ranges')
    ap.add_argument('--out',type=Path,default=Path('/private/tmp/ff-public-cav23'))
    ap.add_argument('--manifest',type=Path,default=Path(__file__).with_name('fixtures')/'cav23-manifest.json')
    args=ap.parse_args()
    if args.archive: archive=args.archive.open('rb')
    else:
        archive=tempfile.TemporaryFile();archive.truncate(SIZE)
        for start,end in RANGES:
            request=urllib.request.Request(URL,headers={'Range':f'bytes={start}-{end}','User-Agent':'QF_FF benchmark downloader'})
            with urllib.request.urlopen(request,timeout=120) as response:
                assert response.status==206
                assert response.headers['Content-Range']==f'bytes {start}-{end}/{SIZE}'
                data=response.read()
            assert len(data)==end-start+1
            archive.seek(start);archive.write(data)
    args.out.mkdir(parents=True,exist_ok=True)
    manifest=dict(source='https://zenodo.org/records/7864537',archive_url=URL,
                  archive_sha256_published='4c326375a6495ce761c9a7c42705d62bf2511998977ef6a635922761a0a79077',
                  integrity='per-entry ZIP CRC and recorded extracted SHA256; whole archive not downloaded',
                  selection='cartesian product: sound/deterministic; none/last/random; circ/zokcirc/zokref; 8 variables; 4/16/64 terms; 255 bits; seed 0',files=[])
    with zipfile.ZipFile(archive) as z:
        for prop,mutation,compiler,terms in itertools.product(['sound','deterministic'],['none','last','random'],['circ','zokcirc','zokref'],[4,16,64]):
            name=f'compilation-{prop}-{mutation}-08v-{terms:03}t-ff-{compiler}-255b-0s.smt2'
            member='docker/benchmarks/benchmarks/'+name
            data=z.read(member)
            (args.out/name).write_bytes(data)
            manifest['files'].append(dict(file=name,member=member,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),property=prop,mutation=mutation,compiler=compiler,terms=terms))
    args.manifest.write_text(json.dumps(manifest,indent=2)+'\n')
    print(f"Extracted and CRC-checked {len(manifest['files'])} benchmarks")


if __name__=='__main__':main()
