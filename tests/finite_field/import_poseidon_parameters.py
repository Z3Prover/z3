#!/usr/bin/env python3
"""Extract width-three fixtures from a downloaded, hash-verified reference tree."""
import argparse
import hashlib
import json
import re
from pathlib import Path

REVISION = '055bde3f4782731ba5f5ce5888a440a94327eaf3'
HASHES = {
    'poseidon.rs': '28eed92696d43200cea4bbe6f5efbf82a7e50691f019d69cea95956a9e01c495',
    'poseidon_instance_bn256.rs': 'd0b93fa452b2e18df3cc0badfe0d7602c37ac377233ae9b02df4306a5fe3fc67',
    'poseidon_instance_bls12.rs': 'f50ca5845ccdc56fba5e6bbb8516dc6494c8c9edae7bd0e7d99c1b8bcaa089b4',
}
FIELDS = {
    'bn254': ('bn256', 21888242871839275222246405745257275088548364400416034343698204186575808495617),
    'bls12_381_scalar': ('bls12', 52435875175126190479447740508185965837690552500527637822603658699938581184513),
}


def extract(directory):
    texts = {}
    for name, digest in HASHES.items():
        data = (directory / name).read_bytes()
        if hashlib.sha256(data).hexdigest() != digest:
            raise ValueError(f'{name}: does not match pinned reference')
        texts[name] = data.decode()
    fields = {}
    for label, (name, prime) in FIELDS.items():
        text = texts[f'poseidon_instance_{name}.rs']
        def matrix(symbol):
            part = text.split(f'pub static ref {symbol}:', 1)[1].split(';', 1)[0]
            entries = re.findall(r'from_hex\("(0x[0-9a-f]+)"\)', part)
            return [entries[i:i+3] for i in range(0, len(entries), 3)]
        mds, constants = matrix('MDS3'), matrix('RC3')
        assert len(mds) == 3 and len(constants) == 64
        tests = texts['poseidon.rs'].split(f'mod poseidon_tests_{name}', 1)[1].split('fn kats()', 1)[1]
        if name == 'bls12':
            tests = tests.split('let poseidon_3 =', 1)[1]
        expected = re.findall(r'from_hex\("(0x[0-9a-f]+)"\)', tests)[:3]
        fields[label] = dict(prime=str(prime), width=3, exponent=5, full_rounds=8,
                             partial_rounds=56, mds=mds, constants=constants,
                             vector_input=[0, 1, 2], vector_output=expected)
    return dict(source=f'https://github.com/HorizenLabs/poseidon2/tree/{REVISION}/plain_implementations/src/poseidon',
                revision=REVISION, source_sha256=HASHES, license='MIT (see POSEIDON-LICENSE-MIT)', fields=fields)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('reference', type=Path)
    parser.add_argument('--out', type=Path, default=Path(__file__).with_name('fixtures') / 'poseidon_t3.json')
    args = parser.parse_args()
    args.out.write_text(json.dumps(extract(args.reference), indent=2) + '\n')
