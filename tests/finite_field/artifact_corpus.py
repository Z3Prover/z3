#!/usr/bin/env python3
"""Inventory whole paper archives, preserving bytes, provenance and duplicates.

Inputs are ZIPs (a sparse ZIP with all benchmark members is sufficient). Docker
images and vendored solver regression suites are not benchmark experiments.
"""
import argparse
import collections
import csv
import hashlib
import io
import json
import re
import tarfile
import zipfile
from pathlib import Path


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cav23', type=Path)
    ap.add_argument('--cav24', type=Path)
    ap.add_argument('--fmcad26', type=Path, help='extracted artifact root')
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / 'inputs').mkdir(exist_ok=True)
    rows, omitted, auxiliary = [], [], {}

    def add(paper, member, data, family, memberships=(), metadata=None):
        sha = hashlib.sha256(data).hexdigest()
        text = data.decode()
        logic = re.search(r'\(set-logic\s+([^\s)]+)', text)
        fields = sorted({int(p) for p in re.findall(r'\(_\s+FiniteField\s+(\d+)\)', text)})
        # Alternate BV/NIA encodings do not exercise either finite-field solver.
        row = dict(paper=paper, member=member, sha256=sha, bytes=len(data),
                   family=family, paper_sets=list(memberships), metadata=metadata or {},
                   logic=logic[1] if logic else None,
                   field_bits=[p.bit_length() for p in fields],
                   checks=len(re.findall(r'\(check-sat\)', text)),
                   declared_status=(re.search(r'\(set-info\s+:status\s+(sat|unsat|unknown)', text) or [None, None])[1])
        if not fields:
            omitted.append(row)
            return
        (args.out / 'inputs' / (sha + '.smt2')).write_bytes(data)
        rows.append(row)

    if args.cav23:
        with zipfile.ZipFile(args.cav23) as z:
            meta = {x['file']: x for x in csv.DictReader(io.StringIO(z.read('docker/benchmarks/benchmarks.csv').decode()))}
            selections = collections.defaultdict(list)
            for selection, member in [('CAV23-full-runs','docker/full_runs.csv'),('CAV23-review-runs','docker/runs.csv')]:
                selected = {r['file'] for r in csv.DictReader(io.StringIO(z.read(member).decode()))}
                auxiliary[selection+'_files'] = len(selected)
                for name in selected: selections[name].append(selection)
            for n in sorted(z.namelist()):
                if not n.endswith('.smt2'): continue
                m = meta.get(Path(n).name, {})
                family = 'TV-' + m.get('ty', '') + '-' + m.get('theory', '') if m else 'Examples'
                add('CAV23', n, z.read(n), family, selections[Path(n).name], metadata=m)
    if args.cav24:
        with zipfile.ZipFile(args.cav24) as z:
            memberships = collections.defaultdict(list)
            for n in z.namelist():
                if n.startswith('experiments/cluster/benchmark_sets/') and not n.endswith('/'):
                    for line in z.read(n).decode().splitlines():
                        memberships['experiments/benchmarks/' + line].append(Path(n).name)
            families = {'circ': 'CirC', 'picus': 'QED2', 'small_field': 'Small', 'craft': 'Seq', 'tx_val': 'TV', 'ashr': 'ASHR'}
            for n in sorted(z.namelist()):
                if not n.endswith('.smt2'): continue
                if n.startswith('experiments/benchmarks/smt2/'):
                    family = families[n.split('/')[3]]
                    if family == 'CirC': family += '-D' if '/deterministic_' in n else '-S'
                else: family = 'Examples'
                add('CAV24', n, z.read(n), family, memberships[n])
            auxiliary['CAV24_non_SMT_completeness_inputs'] = sum(n.endswith('.circ') for n in z.namelist())
            packed = z.read('experiments/benchmarks/zipped_benchmark_files.tar.xz')
            unpacked_hashes = {r['sha256'] for r in rows if r['paper']=='CAV24'}
            packed_count = 0
            with tarfile.open(fileobj=io.BytesIO(packed), mode='r:xz') as tar:
                for item in tar:
                    if item.isfile() and item.name.endswith('.smt2'):
                        data = tar.extractfile(item).read()
                        assert hashlib.sha256(data).hexdigest() in unpacked_hashes, ('additional packed benchmark', item.name)
                        packed_count += 1
            auxiliary['CAV24_packed_SMT_copies_verified_against_unpacked'] = packed_count
    if args.fmcad26:
        extraction = json.loads((args.fmcad26/'extraction.json').read_text())
        auxiliary['FMCAD26_archive_sha256_verified'] = extraction['archive_sha256']
        auxiliary['FMCAD26_Lean_translations_reported_in_readme'] = 1242
        subsets = collections.defaultdict(list)
        for p in args.fmcad26.rglob('benchmark_set*'):
            if p.is_file():
                for line in p.read_text().splitlines():
                    subsets[Path(line.strip()).name].append(p.name)
        for p in sorted(args.fmcad26.rglob('*.smt2')):
            add('FMCAD26', str(p.relative_to(args.fmcad26)), p.read_bytes(),
                p.parent.name, subsets[p.name])
    manifest = dict(sources={'CAV23': 'https://zenodo.org/records/7865471',
                             'CAV24': 'https://zenodo.org/records/10917330',
                             'FMCAD26': 'https://zenodo.org/records/20133205'},
                    integrity='ZIP member CRCs checked when extracting; input SHA256; sparse archives are not whole-archive verified',
                    selection='All finite-field SMT2 benchmark inputs and illustrative examples; alternate BV/NIA encodings catalogued separately',
                    entries=rows, excluded_non_field=omitted, auxiliary_inventory=auxiliary)
    (args.out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print('members', len(rows), 'unique', len({r['sha256'] for r in rows}), 'non-field encodings', len(omitted))
    print(collections.Counter((r['paper'], r['family']) for r in rows))


if __name__ == '__main__':
    main()
