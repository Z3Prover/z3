"""Validate immutable producer evidence and export a source-only handoff."""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).parent
REPO = Path(r'C:\z3seq')
PIN = '71ec455a18702fe695d0c924a535ff9f385bd58d'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def emit(name, value):
    target = ROOT / name
    assert not target.exists(), str(target)
    target.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8', newline='\n')
    return sha(target.read_bytes())


inventory_path = ROOT / 'nfv4-subst-source-inventory.json'
assert sha(inventory_path.read_bytes()) == 'c7d61d859516fda9b404441c625429b0111dc76fec10872beb8602306ddb7456'
inventory = json.loads(inventory_path.read_text())
assert inventory['head'] == PIN
prefix = 'src/ast/seq/'
ranges = {
    prefix + 'seq_eq_facet.cpp': [(35, 68), (109, 151), (373, 403), (1387, 1406)],
    prefix + 'seq_power_facet.cpp': [(27, 60), (85, 92), (179, 265), (814, 885), (900, 936), (1015, 1125), (1180, 1255)],
    prefix + 'seq_mem_facet.cpp': [(975, 1002)],
    prefix + 'seq_power_facet.h': [(86, 118)],
    prefix + 'seq_ambient_context.h': [(140, 159)],
    'src/ast/seq_decl_plugin.cpp': [(1040, 1056)],
}
paths = sorted(ranges)
listing = subprocess.check_output(['git', 'ls-tree', PIN, '--', *paths], cwd=REPO, text=True)
oids = {line.split('\t', 1)[1]: line.split()[2] for line in listing.splitlines()}
assert set(oids) == set(paths)
raw = subprocess.check_output(['git', 'cat-file', '--batch'], input=('\n'.join(oids[p] for p in paths) + '\n').encode(), cwd=REPO)
offset = 0
files = []
by_path = {}
for path in paths:
    end = raw.index(b'\n', offset)
    oid, kind, size = raw[offset:end].decode().split()
    blob = raw[end + 1:end + 1 + int(size)]
    offset = end + 2 + int(size)
    assert kind == 'blob' and oid == oids[path]
    assert hashlib.sha1(b'blob ' + str(len(blob)).encode() + b'\0' + blob).hexdigest() == oid
    text = blob.decode()
    assert REPO.joinpath(*path.split('/')).read_text(encoding='utf-8') == text
    lines = text.splitlines()
    by_path[path] = lines
    indices = sorted({i for a, b in ranges[path] for i in range(a, b + 1)})
    files.append(dict(path=path, blob=oid, sha256=sha(blob), worktree_text_matches=True,
                      ranges=ranges[path], excerpts=[dict(line=i, text=lines[i - 1]) for i in indices]))
assert offset == len(raw)
for old in inventory['files']:
    assert old['blob'] == oids[old['path']]
    for row in old['excerpts']:
        assert by_path[old['path']][row['line'] - 1] == row['text']

# Each entry describes observed source guards, not an assumed global invariant.
specs = {
    ('seq_eq_facet.cpp', 263): ('Reduced element equality; normalized singleton units; distinct values and false ambient equality conflict; unequal characters; orient away from a value.', 'unit(lch) -> [unit(rch)], possibly swapped', 'Reduced sides explicitly eliminate latest bindings before this branch.', 'Parent/equality dependency plus elimination dependencies; ambient equality assumption recorded.'),
    ('seq_eq_facet.cpp', 286): ('Exactly one current side empty; leading unit conflicts; consume leading nonunit token.', 'leading nonunit -> []', 'Reads currently rewritten active equation; no RHS.', 'Current equation dependency; repeated broadcast must shrink the referenced side.'),
    ('seq_eq_facet.cpp', 304): ('Singleton side classified as variable; reject every syntactic occurs(x,t) in copied opposite side.', 'x -> opposite token vector', 'Active equation rewritten by broadcasts; local syntactic occurs check is not transitive latest-binding closure.', 'Current equation dependency; changed flag set.'),
    ('seq_eq_facet.cpp', 396): ('Pending alternative exists; consume next saved alternative.', 'saved variable -> saved replacement', 'No normalization at emission; parent-state restoration for saved alternatives is a separate driver obligation.', 'Saved dependency; optional saved guard asserted after broadcast.'),
    ('seq_eq_facet.cpp', 446): ('Active normalized equation, both widths >=2; one boundary unit; other uninterpreted constant; occurs exclusion; model lengths agree and positive; solver actually implies equal length.', 'uninterpreted constant -> [boundary unit]', 'Uses current active equation and direct occurs exclusion.', 'Join equation and implication dependencies; committed return.'),
    ('seq_eq_facet.cpp', 529): ('Distinct unit characters, not known distinct and not ambient-false; orient toward a constant character if possible.', 'unit token -> [other unit token]', 'Current active equation; exact characters unequal; no latest-binding closure at call.', 'Equation dependency; solver constraint and outer assumption also recorded.'),
    ('seq_eq_facet.cpp', 661): ('Distinct nonunit, nonpower end tokens; choose one of five Nielsen alternatives, reordered but not removed by bounds.', 'v1/v2 -> empty, peer, or peer with keyed fresh remainder', 'Current equation; no explicit transitive occurs guard; keyed freshness is not a new symbol on every invocation.', 'Equation dependency; optional nonempty guard asserted after broadcast; remaining branches saved.'),
    ('seq_eq_facet.cpp', 712): ('One variable-like boundary versus a nonempty unit block; construct saved prefix/extension alternatives.', 'variable-like token -> []', 'Current equation; first branch has no RHS; saved alternatives use units and a keyed fresh remainder.', 'Equation dependency; committed first branch.'),
    ('seq_eq_facet.cpp', 1301): ('Active disequation/memberships; qualifying peer star; bounded product witness succeeds and rewrites to a string literal.', 'endpoint -> concrete literal units', 'Literal RHS; helper does not locally enforce uninterpreted endpoint; parent/iterator eligibility still matters.', 'New reversible completion equality assumption dependency.'),
    ('seq_eq_facet.cpp', 1379): ('Active disequation; same nonempty view sets; positive unsigned bounded model length; two different longer literal witnesses.', 'left endpoint -> first concrete literal units', 'Literal RHS; no global substitution closure or local endpoint-kind check.', 'New reversible completion equality assumption dependency.'),
    ('seq_eq_facet.cpp', 1711): ('Completion not blocked; collected nonvalue candidate; candidate concrete elements/literal or empty; optional negative-assumption rejection; block repeat completion.', 'candidate token -> model value units/empty', 'Candidate terms include symbolic units/selectors; dependent terms rewritten from selected model values; no get_subst at emission.', 'Each candidate gets an equality assumption; join dependencies for returned edge.'),
    ('seq_power_facet.cpp', 124): ('Active power whose current base is syntactic empty.', 'power token -> []', 'No RHS; active obligation selected.', 'Stored power dependency; power sink deactivates matching key.'),
    ('seq_power_facet.cpp', 138): ('Active power; syntactic numeral exponent <=1024; positive unfolds, nonpositive empty.', 'power token -> current base repeated positive exponent times, else []', 'Current mutable base, not original AST base; no self/closure exclusion.', 'Stored power dependency; power sink deactivates matching key.'),
    ('seq_power_facet.cpp', 200): ('Active indexed power; next enumeration j <= bound (residual emits no substitution).', 'power token -> current base repeated j times', 'Saved iterator index checked active; j starts with positive enumeration; no base-cycle exclusion.', 'Saved dependency; exponent=j constraint added after broadcast.'),
    ('seq_power_facet.cpp', 212): ('Helper invoked by power_split::split at257 or power_peel::split at885 after their trigger guards.', 'selected power token -> []', 'Copies obligation; no RHS; callers independently check activity/presence.', 'Caller dependency; exponent<=0 constraint added after broadcast.'),
    ('seq_power_facet.cpp', 508): ('power_trichotomy case0 in either direction; length ordering and empty-power disjunction constraints.', 'shorter power token -> []', 'Copies active trigger obligations; no RHS.', 'Trigger dependency; conditional branch constraints, not proved concrete assignments.'),
    ('seq_power_facet.cpp', 578): ('power_trichotomy cases1-4 with their actual equations/arithmetic constraints.', 'longer power token -> shorter power token followed by residual', 'Copies mutable bases; registers residual powers; keyed fresh terms; no global closure check. P18 identity proof remains open.', 'Trigger dependency; local equations/constraints inherit it.'),
    ('seq_power_facet.cpp', 802): ('Active axiomatized symbolic exponent; model value<=1024; solver implies that exact integer value.', 'power token -> positive copies of current base, else []', 'Mutable current base used; no self/closure guard.', 'Join stored and implication dependencies; committed return.'),
    ('seq_power_facet.cpp', 862): ('Saved power/equation indices in bounds and active; positive peel alternative.', 'power token -> current base plus power(current base,n-1), directionally', 'Copies obligation; new arithmetic exponent normalized; no self-base exclusion.', 'Saved equation dependency; n>=1 asserted after broadcast.'),
    ('seq_power_facet.cpp', 987): ('Current decomposition boundary; preceding power boundary skipped; original power found active. Caller requires entire original base be unit tokens.', 'variable -> power(base,fresh_m) plus prefix and optional inner power', 'Saved unit-only base excludes direct variable-token self-base candidate; no complete latest-binding DAG proof.', 'Saved equation dependency; fresh_m>=0 and proper-prefix inequalities after broadcast.'),
    ('seq_power_facet.cpp', 1007): ('All decomposition positions exhausted; extension not yet offered.', 'variable -> original power token plus keyed fresh tail, directionally', 'Caller unit-only base guard; original power token retained from saved parent state; no latest-binding closure.', 'Saved dependency; tail length>=0 asserted after broadcast.'),
    ('seq_power_facet.cpp', 1168): ('Gpower self-cycle trigger; nonempty compressed prefix; optional single-power unwrap; iterator boundary exists.', 'variable -> registered fresh-exponent power plus prefix/optional inner power', 'Unwrapped base need not remain ground: variable may become that base. No occurs/acyclicity guard on this result.', 'Saved equation dependency; fresh exponent>=0 and optional inner bounds after broadcast.'),
    ('seq_mem_facet.cpp', 1030): ('Saved membership/power indices in bounds and active; positive peel alternative.', 'power token -> current base plus power(current base,n-1), directionally', 'Copies mutable current base; exponent subtraction not normalized here; no self-base exclusion.', 'Saved membership dependency; n>=1 asserted after broadcast.'),
    ('seq_mem_facet.cpp', 1055): ('Active membership with symbolic active power at directional end.', 'power token -> []', 'Copies selected obligation; no RHS.', 'Membership dependency; n<=0 asserted after broadcast.'),
}
producers = []
for row in inventory['producers']:
    key = (row['path'].rsplit('/', 1)[-1], row['line'])
    guard, replacement, normalization, dependency = specs.pop(key)
    assert by_path[row['path']][row['line'] - 1].strip() == row['text']
    producers.append(dict(**row, guard=guard, replacement=replacement,
                          normalization=normalization, dependency_and_activity=dependency,
                          global_latest_binding_dag_proved=False))
assert not specs and len(producers) == 24
assert len({(p['path'], p['line']) for p in producers}) == 24
scopes = {(p['path'], p['function'], p['first'], p['last']) for p in producers}
assert len(scopes) == 16
extra_sha = emit('nfv4-subst-extra-source.json', dict(head=PIN, files=files,
    note='Exact immutable excerpts; missing seq_decl paths during lookup were corrected to seq_decl_plugin, with no alternate restricted-file access.'))
chains = [
    dict(id='C11-chain1', result='blocked in the simple active-equation scenario',
         sequence=['Start X=Y.A and Y=X.B with no prior bindings.',
                   'After X->[Y,A], active second equation is Y=Y.A.B.',
                   'simplify_equation rejects Y as a definition because occurs(Y,Y) holds.'],
         limit='Does not prove arbitrary producer histories or global acyclicity.'),
    dict(id='C11-chain2', result='blocked by inspected decomposition caller guard',
         sequence=['Attempt variable decomposition of X against power(X,n).',
                   'find_var_decompose_trigger requires every flattened current base token be a unit.',
                   'A sequence variable X is not a unit, so this attempted trigger is rejected.'],
         limit='This rejection does not apply to the different gpower producer.'),
    dict(id='C11-chain3', result='conditional local source chain; full driver reachability unproved',
         prestate=['Active equation [P,X]=[X,unit(a)], P=power(X,n), n symbolic, P registered active with current base X.',
                   'Choose first gpower fresh-key use for X, yielding fresh integer k and Q=power(X,k), distinct from P. No prior substitutions are needed.'],
         sequence=['Forward gpower trigger scans prefix [P] before target X; opposite head is X.',
                   'Single-power unwrap changes compressed prefix [P] to its current base [X]; non-groundness is not rechecked.',
                   'split registers Q with base X before invoking its iterator.',
                   'First iterator position has plain token X and empty prefix, so line1168 broadcasts X->[Q].',
                   'power_facet::apply_subst scans active P and Q and replaces base token X with Q; both current bases become Q, including Q itself.',
                   'Conditional extension: if power_fixed_exp is called with solver implication k=1, line802 emits Q->[Q], because one-copy unfold returns the current base Q.',
                   'Conditional extension: eliminating Q with that latest binding repeats the same token; removal-before-membership is not an ancestor guard.'],
         distinctions=['Q.m_e remains finite original AST power(X,k); mutable Q.m_s==Q is not a cyclic AST pointer structure.',
                       'The active-power current-base dependency graph can self-reference before any self-edge exists in m_subst.',
                       'A later Q->[Q] would create a latest-binding self-edge; it has additional caller/implication premises.'],
         limit='No claim that propagation order, splitter priority, implication queries, backtracking and later elimination jointly reach this state in the native solver; no native run, hang or crash observed.'),
]
ledger_sha = emit('nfv4-subst-producer-ledger.json', dict(
    head=PIN, comparison_master=inventory['master'], previous_publication=inventory['previous_publication'],
    stage='nfv4-subst-invariants', classification='source-only',
    source_inventory_sha256=sha(inventory_path.read_bytes()), extra_source_sha256=extra_sha,
    producers=producers, concrete_chain_attempts=chains,
    sink_facts=[
        'subst_in replaces whole equal tokens only, not arbitrary AST subterms.',
        'eq sink rewrites all active equations and appends/trails a latest binding; old RHS vectors remain untouched.',
        'power sink removes active matching keys, adds replacement powers, then rebases all active current bases mentioning the variable.',
        'find_power ignores inactive entries; add_power therefore can register a term again after deactivation. Its idempotence is active-only.',
        'Keyed fresh cache returns a retained fresh constant for repeated identical caller/sort/argument keys, not a new constant per invocation.',
        'Central broadcast has no occurs/DAG guard and adds a length constraint after all sinks.',
        'mem sink snapshots the old membership count before remove/add; does not revisit appended entries in that pass.',
        'unfold_empty has exactly the two direct callers at power cpp257 and885 in the pinned source.',
    ],
    source_tool_validation_history=inventory['validation_history'],
    formal_properties_selected=0, verifier_attempts=0, native_executions=0,
    unresolved=['Global latest-binding DAG preservation across all producers and restored iterator states.',
                'Native search-driver eligibility and scheduling for chain3 and any subsequent self-binding/elimination.',
                'Concrete-value terminality and exact endpoint eligibility across completion helper callers.'],
    selection_handoff='Consider a new whole-entry power_facet::apply_subst invariant-preservation intent with explicitly modeled complete sink effects and the chain3 caller context. Do not select or claim a refutation until the independent core stage and frozen selection.'))
report = ROOT / 'nfv4-subst-invariants.md'
assert report.exists()
report_sha = sha(report.read_bytes())
handoff_sha = emit('nfv4-subst-handoff.json', dict(stage='nfv4-subst-invariants', status='done',
    inventory_sha256=sha(inventory_path.read_bytes()), extra_source_sha256=extra_sha,
    producer_ledger_sha256=ledger_sha, report_sha256=report_sha,
    producer_calls=24, producer_scopes=16, concrete_chain_attempts=3,
    next_stage='nfv4-core-provenance', schedule_id=2, stop_schedule=False))
print(json.dumps(dict(status='pass', producer_calls=24, producer_scopes=16,
    additional_capture_files=len(files), additional_exact_lines=sum(len(f['excerpts']) for f in files),
    chain_attempts=3, verifier_attempts=0, report_sha256=report_sha,
    producer_ledger_sha256=ledger_sha, handoff_sha256=handoff_sha), indent=2))
