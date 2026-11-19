"""Read-only provenance/metadata checks for a locally translated NFV-style audit.

This is not the upstream NFV validator and does not prove translation fidelity.
Only git object reads and local artifact reads are performed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--models', type=Path, default=Path(__file__).parent / 'nfv2-models')
args = parser.parse_args()
props = json.loads((args.models / 'properties.json').read_text(encoding='utf-8'))
head = '71ec455a18702fe695d0c924a535ff9f385bd58d'
sources = {}
summaries = []
for prop in props:
    path = args.models / (prop['id'] + '.dfy')
    raw = path.read_bytes()
    model = raw.decode('utf-8')
    assert hashlib.sha256(raw).hexdigest() == prop['sha256'], (prop['id'], 'hash mismatch')
    code = re.sub(r'//[^\n]*', '', model)
    assert not re.search(r'\b(assume|expect|include|import|export|module|extern|abstract|opaque|iterator|yield|const|type|newtype|trait|codatatype)\b', code), prop['id']
    assert '{:' not in code and not re.search(r'\bdecreases\s+\*',code), prop['id']
    assert not re.search(r'\bNfv\w*',code), prop['id']
    pending = False
    synthetic = False
    tags = 0
    for row in model.splitlines():
        if not row.strip():
            continue
        tag = re.fullmatch(r'// src: ([^:]+):(\d+) \| (.*)', row)
        if tag:
            name, number, quote = tag.groups()
            if name not in sources:
                sources[name] = subprocess.check_output(['git','show',head+':'+name],text=True,encoding='utf-8').splitlines()
            assert sources[name][int(number)-1].strip() == quote, (prop['id'], row)
            assert name in prop['required_context'], (prop['id'], 'undeclared context')
            pending, synthetic = True, False
            tags += 1
        elif row.startswith('// synth: '):
            assert not pending, (prop['id'], 'discarded source tag')
            pending, synthetic = True, True
        else:
            assert pending, (prop['id'], 'untagged line',row)
            if synthetic:
                assert re.fullmatch(r'[{};]+|(?:requires|ensures|invariant|assert|decreases|reads|modifies)\b.*',row.strip()), (prop['id'],'synthetic computation',row)
            pending = False
    assert not pending, (prop['id'],'dangling tag')
    signature = code[code.index('method '+prop['entry_point']):].split('\n{',1)[0]
    assert re.findall(r'^\s*ensures (.+)$',signature,re.M) == prop['original_ensures'], prop['id']
    assert re.findall(r'^\s*requires (.+)$',signature,re.M) == [a['clause'] for a in prop['assumptions']], prop['id']
    declared = set(re.findall(r'^\s*(?:ghost\s+)?(?:method|function|predicate|lemma)\s+(\w+)\(',code,re.M)) - {prop['entry_point']}
    assert declared == {e['name'] for e in prop['environment']}, (prop['id'],'helper metadata')
    assert prop['quote'] in '\n'.join(sources[prop['path']]), (prop['id'],'quote absent')
    assert prop['witnesses'], (prop['id'],'no domain examples')
    summaries.append(dict(id=prop['id'],source_tags=tags,requires=len(prop['assumptions']),helpers=len(declared),sha256=prop['sha256']))
print(json.dumps(dict(status='pass',scope='exact tags, metadata, forbidden constructs; NOT source equivalence or full upstream validation',properties=summaries),indent=2))
