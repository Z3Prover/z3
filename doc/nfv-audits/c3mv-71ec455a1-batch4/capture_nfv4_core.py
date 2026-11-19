"""Capture at most sixteen immutable files for the core provenance stage."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).parent
REPO = Path(r'C:\z3seq')
PIN = '71ec455a18702fe695d0c924a535ff9f385bd58d'
RANGES = {
    'src/util/stx_search_tree.h': [(119, 156), (175, 200), (340, 363), (424, 447), (570, 618), (630, 659), (743, 850), (1070, 1169), (1334, 1378)],
    'src/util/dependency.h': [(45, 80), (190, 275), (370, 403)],
    'src/ast/seq/seq_ambient_context.h': [(61, 119), (175, 187), (260, 270)],
    'src/smt/seq_solver_facet.cpp': [(28, 137), (145, 159), (219, 265)],
    'src/smt/seq_solver_facet.h': [(113, 140)],
    'src/smt/theory_nseq.cpp': [(159, 232), (341, 398), (410, 550), (735, 773), (815, 849), (1128, 1158)],
    'src/ast/seq/seq_eq_facet.cpp': [(85, 108), (189, 309), (349, 367), (506, 522), (738, 782), (925, 977), (990, 1047), (1102, 1135)],
    'src/ast/seq/seq_eq_facet.h': [(130, 157), (200, 212), (354, 373), (405, 413)],
    'src/ast/seq/seq_mem_facet.cpp': [(297, 345), (364, 398), (640, 715), (726, 820), (826, 972), (1280, 1310), (1585, 1610), (1820, 1857), (1928, 1999)],
    'src/ast/seq/seq_mem_facet.h': [(65, 94), (168, 186), (216, 245)],
    'src/ast/seq/seq_ncontains_facet.cpp': [(79, 108), (225, 285), (350, 369)],
    'src/ast/seq/seq_ncontains_facet.h': [(60, 79), (143, 153)],
    'src/ast/seq/seq_power_facet.h': [(125, 136)],
    'src/ast/seq/seq_assumption_facet.h': [(30, 87)],
    'src/ast/seq/seq_req_facet.cpp': [(62, 103)],
    'src/ast/seq/seq_lex_facet.cpp': [(110, 218)],
}
assert len(RANGES) == 16


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write(name, value):
    target = ROOT / name
    assert not target.exists(), str(target)
    target.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8', newline='\n')
    return sha(target.read_bytes())


paths = sorted(RANGES)
listing = subprocess.check_output(['git', 'ls-tree', PIN, '--', *paths], cwd=REPO, text=True)
oids = {line.split('\t', 1)[1]: line.split()[2] for line in listing.splitlines()}
assert set(oids) == set(paths)
raw = subprocess.check_output(['git', 'cat-file', '--batch'], input=('\n'.join(oids[p] for p in paths) + '\n').encode(), cwd=REPO)
offset = 0
files = []
sites = []
sources = {}
for path in paths:
    end = raw.index(b'\n', offset)
    oid, kind, size = raw[offset:end].decode().split()
    blob = raw[end + 1:end + 1 + int(size)]
    offset = end + 2 + int(size)
    assert oid == oids[path] and kind == 'blob'
    assert hashlib.sha1(b'blob ' + str(len(blob)).encode() + b'\0' + blob).hexdigest() == oid
    text = blob.decode()
    assert REPO.joinpath(*path.split('/')).read_text(encoding='utf-8') == text.replace('\r\n', '\n'), path
    lines = text.splitlines()
    sources[path] = text
    indices = {i for a, b in RANGES[path] for i in range(a, b + 1)}
    disabled_spans = [(m.start(), m.end()) for m in re.finditer(r'^\s*#if 0\b.*?^\s*#endif\b', text, re.M | re.S)]
    if path.endswith('.cpp') and path != 'src/smt/theory_nseq.cpp':
        for match in re.finditer(r'^.*\bn\.set_conflict\([^\n]*', text, re.M):
            line = text.count('\n', 0, match.start()) + 1
            disabled = any(a <= match.start() < b for a, b in disabled_spans)
            sites.append(dict(path=path, line=line, text=match.group().strip(), compile_time_disabled=disabled))
            indices.update(range(max(1, line - 12), min(len(lines), line + 8) + 1))
    assert min(indices) >= 1 and max(indices) <= len(lines)
    files.append(dict(path=path, blob=oid, sha256=sha(blob), worktree_universal_newline_matches=True,
                      raw_blob_crlf_count=blob.count(b'\r\n'),
                      excerpts=[dict(line=i, text=lines[i - 1]) for i in sorted(indices)]))
assert offset == len(raw)
assert len(sites) == 27, len(sites)
assert [(s['path'], s['line']) for s in sites if s['compile_time_disabled']] == [('src/ast/seq/seq_mem_facet.cpp', 785)]

# Reuse the previously captured power producer rather than expanding this stage.
old_path = ROOT / 'nfv4-subst-source-inventory.json'
old = json.loads(old_path.read_text())
assert old['head'] == PIN
power = next(f for f in old['files'] if f['path'].endswith('seq_power_facet.cpp'))
power_row = next(r for r in power['excerpts'] if r['line'] == 164)
assert power_row['text'].strip() == 'n.set_conflict(stx::br_plugin_base, sf.conflict_dep());'
sites.append(dict(path=power['path'], line=164, text=power_row['text'].strip(),
                  compile_time_disabled=False, reused_inventory_sha256=sha(old_path.read_bytes())))

registry = re.findall(r'register_facet_bound<seq::(\w+)>', sources['src/smt/theory_nseq.cpp'])
assert len(registry) == 12, registry
assert subprocess.check_output(['git', 'rev-parse', 'HEAD:src'], cwd=REPO, text=True).strip() == 'caa5a9922f074f9f4adc8f7c98e1685be9626503'
source_sha = write('nfv4-core-source-inventory.json', dict(head=PIN,
    comparison_master='c2460a558fc6fee3cf15cfebd2d3f642ebf77770', files=files,
    registration_order=registry, facet_conflict_sites=sites,
    scope='Sixteen newly captured files and one reused pinned power-conflict site; not all transitive helper implementations.',
    capture_limit=16, validation_failures=[dict(
        result='Initial capture assertion failed before any evidence output; not a verifier check.',
        cause='seq_lex_facet.cpp has 536 CRLF line endings in its pinned Git blob; read_text normalizes them.',
        diagnostic='All sixteen files checked; this was the only mismatch and universal-newline equality passed.',
        correction='Normalize CRLF only for worktree-text comparison; retain raw Git blob hash and CRLF count. No source bytes changed.',
        runner_note='The initial compound shell returned the later git command status despite the Python exception; the corrected run propagates Python failure before git inspection.')]))

ledger_sha = write('nfv4-core-provenance-ledger.json', dict(
    head=PIN, stage='nfv4-core-provenance', classification='source-only',
    source_inventory_sha256=source_sha,
    direct_conflict_sites=dict(textual=len(sites), active=27, disabled=1),
    dependency_facts=[
        dict(source='src/util/dependency.h:190-275', fact='Null denotes empty dependency; join(null,d)=d; joining does not invent leaves; contains/linearize traverse existing leaf values.'),
        dict(source='src/ast/seq/seq_ambient_context.h:113-119; src/smt/theory_nseq.cpp:739-743,815-844', fact='Conditional expression indices use even leaf values; outer assumptions use odd values. Outer reporting negates required conditional literals as well as root assumptions.'),
        dict(source='src/smt/seq_solver_facet.cpp:43-106', fact='Null-dependency assertions are unconditional; nonnull assertions are guarded by retained assumption literals. UNSAT joins only returned active assumption dependencies; null can mean contradiction using only unconditional facts.'),
        dict(source='src/util/stx_search_tree.h:424-443,775-799', fact='Non-null node conflicts accumulate; clear_status does not erase the history. Null conflict skips filtering; null fact handles are conservatively retained.'),
        dict(source='src/util/stx_search_tree.h:1145-1158,1345-1358', fact='All-child closure joins the solve-wide conflict history, not only siblings; this over-includes prior leaves. Cache/store/watch lists and conflict history are cleared at each solve entry.'),
    ],
    producer_families=[
        dict(family='equations/disequations', sites=[363,518,777,1131], file='seq_eq_facet.cpp', evidence='Current fact dependency; ambient-false joins; approximation joins equation with reported used-membership dependencies; identical disequation sides use current disequation dependency.', gap='Correctness and complete used-premise reporting of reducers/approximator remain transitive obligations.'),
        dict(family='memberships', file='seq_mem_facet.cpp', evidence='Own membership for structural clashes; joined view/monadic core handles; arithmetic core; joined length/letter conflicts. Line785 is disabled under #if0, not an active producer.', gap='view_witness, monadic oracle, letter abstraction and whole length encoding are not semantically verified in this bounded stage.'),
        dict(family='negative containment', file='seq_ncontains_facet.cpp', sites=[235,251,282,364], evidence='Own dependency for empty needle or determined match; joins with equation for exposed infix; joins ambient-false finite mismatch clause.', gap='Prior model-only containment refutations/native applicability limits remain separate.'),
        dict(family='request and lexicographic', files=['seq_req_facet.cpp','seq_lex_facet.cpp'], evidence='Regex verdict conflicts use request dependency; lexical simplification returns current obligation dependency, cycle helper returns its joined dependency.', gap='Bisimulation/cycle-helper correctness and every excluded facet lifecycle are not proved here.'),
        dict(family='arithmetic and power forwarding', evidence='Arithmetic propagation and power propagation forward solver conflict dependencies.', gap='Solver correctness and semantic relation between mutable power bases and signature terms remain external.'),
    ],
    cache_observations=[
        'Contributing signatures are active equations, disequations, memberships and negative containments; value clones intentionally omit dependency handles.',
        'Default excluded facets block only when is_satisfied returns false. Backend satisfaction means SAT, not no live constraints. Power and assumption facets always return true.',
        'Eligibility therefore is not itself a proof that omitted live state is irrelevant; fixed background versus branch-local premises must be justified.',
        'Cache scope is one solve call, including iterative-deepening rounds. Cross-solve or across-outer-assignment cache persistence is not an established concern.',
        'A dependency leaf may refer to a temporary exact-length view rather than a signature constraint. Subset inclusion does not put that premise into a cached core.',
        'The prior P19 identity mismatch can suppress multi-literal hits; a questionable stored core is not automatically a reachable wrong pruning result.',
    ],
    conditional_length_candidate=dict(
        languages=[['a','bb'],['b','bb']], common_word='bb', model_length=1,
        premises=['Two active single-variable plain memberships; no sequence equations/disequations pending; witness not yet extracted.',
                  'Extraction path enabled, monadic endgame skipped/unknown, no earlier splitter/propagation changes this state; backend supplies length model 1 and remains SAT.',
                  'Witness helper returns a correct negative result for the two memberships conjoined with length=1 and reports all corresponding dependency handles.',
                  'No other excluded facet rejects cache eligibility.'],
        source_chain=['mem cpp886-903 reads model length, allocates a conditional dependency and adds an untrailed exact-length view only to the witness helper.',
                      'mem cpp906-913 joins that helper core and sets node conflict; scope exit shrinks away temporary views.',
                      'mem_witness_split returns with node conflict; stx extend/dfs closure can call cache_insert after its scoped split guard unwinds.',
                      'compute_constraints sees active memberships, not the temporary view; both membership leaf sets are subsets of the conflict leaf union.',
                      'The recorded membership-only set still has the word bb; a correct length-conditional contradiction is not an unconditional membership contradiction.'],
        status='Meaningful source-grounded sufficiency gap and concrete mathematical candidate, not an accepted NFV refutation.',
        native_gaps=['Earlier word-template/monadic/splitter processing; actual arithmetic model choice; complete witness core production; actual insertion/hit path.',
                     'No proof that defaults or any user-level SMT-LIB input reach this exact path; no native execution or false SAT/UNSAT result observed.']),
    selection_handoff=[
        'Consider a whole-entry cache_insert semantic sufficiency/state-effect intent, with finite-language membership semantics defined in bodies and independently checked length-conditional closure, not an assumed unsat-core oracle.',
        'Include real admission/filter/intern/watch effects and distinguish temporary premises from fixed per-solve background; preserve the complete original goal after freezing.',
        'If that translation cannot justify its caller domain, defer semantic cache soundness rather than replace it with a leaf-subset/eligibility theorem.',
        'Retain the separate whole-entry power substitution candidate from the completed source stage. Registry order puts power_peel before gpower; the earlier candidate still has a driver reachability gap.',
    ],
    formal_properties_selected=0, verifier_attempts=0, native_executions=0))
report_sha = sha((ROOT / 'nfv4-core-provenance.md').read_bytes())
handoff_sha = write('nfv4-core-handoff.json', dict(stage='nfv4-core-provenance', status='done',
    source_inventory_sha256=source_sha, provenance_ledger_sha256=ledger_sha,
    report_sha256=report_sha, next_stage='nfv4-select', schedule_id=2, stop_schedule=False))
print(json.dumps(dict(status='pass', newly_captured_files=16,
    exact_lines=sum(len(f['excerpts']) for f in files), textual_conflict_sites=len(sites),
    active_conflict_sites=27, disabled_conflict_sites=1, registered_facets=len(registry),
    source_inventory_sha256=source_sha, provenance_ledger_sha256=ledger_sha,
    report_sha256=report_sha, handoff_sha256=handoff_sha), indent=2))
