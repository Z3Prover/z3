"""Load the frozen Z3 journal with explicitly recorded compatibility reruns."""
import json
from pathlib import Path

DATA = Path(__file__).resolve().parent / 'results/cav-overview'


def current_rows():
    rows = {}
    for line in (DATA / 'z3-runs.jsonl').read_text().splitlines():
        row = json.loads(line)
        assert row['sha256'] not in rows
        rows[row['sha256']] = row
    directory = DATA / 'examples-normalized'
    metadata = json.loads((directory / 'metadata.json').read_text())
    original = json.loads((DATA / 'metadata.json').read_text())
    for key in ('binary_sha256', 'timeout', 'memory_mib'):
        assert metadata[key] == original[key], key
    for row in json.loads((directory / 'runs.json').read_text()):
        if not row['removed_incremental']:
            continue
        h = row['sha256']
        assert h in rows
        rows[h] = dict(row, solver='z3', input_sha256=row['normalized_sha256'],
                       measurement_source='examples-normalized (one worker)',
                       original_result=rows[h]['result'])
    return rows
