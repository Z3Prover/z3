"""Freeze source-grounded intents and concrete inputs before Dafny modeling."""
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).parent
REPO = Path(r'C:\z3seq')
PIN = '71ec455a18702fe695d0c924a535ff9f385bd58d'
BASE = '437536cd64a544a1c329fc57d83e56e294fdf47c'
MASTER = 'c2460a558fc6fee3cf15cfebd2d3f642ebf77770'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def emit(name, data):
    path = ROOT / name
    assert not path.exists(), str(path)
    path.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8', newline='\n')
    return sha(path.read_bytes())


def domain(predicate, reason):
    return dict(predicate=predicate, origin='inferred', optional=False, justification=reason)


def helper(name, meaning, source):
    return dict(name=name, body_required=True, semantics=meaning, source=source)


def example(label, inputs, feature):
    return dict(label=label, inputs=inputs, purpose=feature, status='unverified concrete domain candidate, not an outcome')


handoffs = {}
for name, expected in [
    ('nfv4-subst-handoff.json', 'caea281691e4f3aa45a0c645a89a09c1e02b7dc44c074e45d921ad671b72c2fb'),
    ('nfv4-core-handoff.json', 'a1c172a2f50cdeba4b943ae5d40fffcff438e6eaa0058787bddc71c71e0ebfa2'),
]:
    blob = (ROOT / name).read_bytes()
    assert sha(blob) == expected
    handoffs[name] = expected
    assert json.loads(blob)['status'] == 'done'

p20_inputs = dict(
    syntaxPower='seq<bool>', syntaxWidths='seq<int>', syntaxItems='seq<int>', syntaxExps='seq<int>',
    keys='seq<int>', widths='seq<int>', items='seq<int>', active='seq<bool>',
    exps='seq<int>', deps='seq<int>', flags='seq<int>', fromTok='int', repl='seq<int>', substDep='int')
p20_main = dict(syntaxPower=[False, True, True], syntaxWidths=[0, 1, 1], syntaxItems=[0, 0], syntaxExps=[0, 10, 11],
    keys=[1, 2], widths=[1, 1], items=[0, 0], active=[True, True], exps=[10, 11], deps=[1, 1], flags=[1, 0],
    fromTok=0, repl=[2], substDep=1)
p20_empty = copy.deepcopy(p20_main)
p20_empty['repl'] = []
p20_append = copy.deepcopy(p20_main)
p20_append.update(keys=[1], widths=[1], items=[0], active=[True], exps=[10], deps=[7], flags=[3], fromTok=1, repl=[2], substDep=5)
p20_repeat = copy.deepcopy(p20_main)
p20_repeat.update(keys=[2], widths=[1], items=[0], active=[True], exps=[11], deps=[9], flags=[3], fromTok=2, repl=[2, 2], substDep=9)
p20 = dict(id='P20', coverage_candidate='C11-current-base-invariant', path='src/ast/seq/seq_power_facet.cpp',
    entry='power_facet::apply_subst', entry_needle='void power_facet::apply_subst(',
    entry_name='PowerSubstitutionEntry', quote_needle='// rebase obligations whose base mentions var; the power token keeps its identity',
    inputs=p20_inputs,
    input_meaning=dict(
        syntaxPower='Finite immutable AST-token catalog: power classification. IDs are pointer-equality classes, not interpreted words.',
        syntaxWidths='Per-token flattened ORIGINAL AST base widths; zero for nonpowers.',
        syntaxItems='Flattened original AST base tokens, each in the catalog.',
        syntaxExps='Original exponent AST identity per token; only power entries are observed.',
        keys='Append-only obligation term tokens; inactive duplicate keys allowed.',
        widths='Per-record flattened CURRENT mutable base widths.', items='Flattened current mutable bases.',
        active='Record activity.', exps='Record exponent AST identities.', deps='Opaque dependency handles; zero is null.',
        flags='Bit0 axiomatized, bit1 split_exhausted.', fromTok='Substituted token.', repl='Flat replacement tokens.',
        substDep='Observed incoming dependency handle; this source entry deliberately ignores it.'),
    outputs=dict(keysOut='seq<int>', widthsOut='seq<int>', itemsOut='seq<int>', activeOut='seq<bool>',
                 expsOut='seq<int>', depsOut='seq<int>', flagsOut='seq<int>'),
    domain=[
        domain('Catalog arrays have matching lengths; widths are nonnegative and sum to item count; every token ID is in range; nonpower syntax widths are zero; immutable original-power/base graph is acyclic.', 'Finite immutable AST projection and flattened-token API; no decreasing rank or mutable-graph acyclicity is assumed.'),
        domain('Record arrays have matching lengths; base widths partition items; keys are syntactic powers; current bases/replacement/fromTok are valid catalog tokens; active keys are unique; record exponents equal their key catalog exponents.', 'Well-formed private power vector and find_power/add_power representation; does not imply a DAG of current bases.'),
        domain('Dependency handles are nonnegative; flags are in0..3; record count plus replacement count and every possible rewritten individual base width remain below2^32.', 'Opaque null/non-null projection, two source booleans and representable unsigned vector loops under successful allocation. No arbitrary small-instance cap.'),
    ],
    whole_positive_property='PowerStateWellFormed(out) && PowerUpdateExact(in,out) && (CurrentBaseAcyclic(in) ==> CurrentBaseAcyclic(out))',
    positive_meaning='Complete remove/register/rebase update preserves structural representation and metadata, and preserves a cycle-free active current-base dependency graph when the input graph is cycle-free. The last implication is an explicit source-inferred hypothesis, not a proved caller invariant.',
    computation=[
        'Copy all record columns. Find first ACTIVE record with key=fromTok and deactivate it, retaining all other fields and old indices.',
        'For EACH replacement token in order: if syntactically a power, find an active equal key; if absent append a record with its ORIGINAL syntax base/exponent, null dependency, both flags false, active true. Inactive equal keys do not prevent appending.',
        'Scan the full resulting dynamic vector, including appended records. For each ACTIVE record whose flattened current base contains fromTok, replace every whole matching token with repl, preserving token order. No recursive AST substitution and no implicit normalization through eq_facet bindings.',
        'The source ignores substDep and does not change other facets, append an eq_facet substitution, or enforce new arithmetic guards here.',
    ],
    required_helpers=[
        helper('FindActive/RegisterPower', 'Body-defined first-active lookup and idempotent-while-active registration with all constructor fields.', 'seq_power_facet.h:38-61,86-118'),
        helper('FlatSubstitute', 'Replace exact token identities once in the old base, not recursively in newly inserted tokens.', 'seq_eq_facet.cpp:37-45'),
        helper('CurrentBaseAcyclic', 'Exact finite-graph cycle predicate on active keys and their current base tokens; a bounded finite-graph algorithm is allowed only with a completeness argument, not execution fuel or assumed rank.', 'seq_power_facet.cpp:49-59; seq_eq_facet.cpp:128-150'),
        helper('PowerUpdateExact', 'Body-defined full relation covering old index/key/exponent/dependency/flag preservation, exact deactivation, ordered registrations/defaults and exact flattened base replacement for all active records.', 'seq_power_facet.cpp:43-60'),
    ],
    examples=[example('gpower-pre-registered-bases', p20_main, 'P and Q both initially base X; replacing X with Q exercises self-rebasing without assuming a cyclic input.'),
              example('erase-bases', p20_empty, 'Empty replacement, no registration.'),
              example('deactivate-then-register', p20_append, 'Retain inactive record and append an absent replacement power with default metadata.'),
              example('repeat-active-key', p20_repeat, 'Deactivation followed by repeated same-key replacement registers only one new active record.')],
    limitations=['Mutable-base acyclicity is not AST pointer acyclicity or latest eq_facet-binding acyclicity.',
                 'No native reachability of the gpower producer prestate, later self-binding, elimination, hang or crash is established; power_peel is registered earlier than gpower.',
                 'Successful allocation/trailing and flatten/concat projection are modeled, not native lifetime, allocator failure, cancellation or C++ equivalence.'])

p21_inputs = dict(enabled='bool', facetContrib='seq<bool>', facetSatisfied='seq<bool>', facetWidths='seq<int>', facetValues='seq<int>',
    factHasDep='seq<bool>', factDepWidths='seq<int>', factDepItems='seq<int>', conflictHasDep='bool', conflictLeaves='seq<int>',
    wordWidths='seq<int>', wordChars='seq<int>', langWidths='seq<int>', langWords='seq<int>', backgroundAny='bool', backgroundLengths='seq<int>',
    guessPresent='bool', guessLength='int', guessLeaf='int', proofPositions='seq<int>',
    store='seq<int>', coreWidths='seq<int>', coreIds='seq<int>', coreWatch='seq<int>', bucketWidths='seq<int>', bucketItems='seq<int>')
p21_main = dict(enabled=True,
    facetContrib=[True, True, False, False, True, True, False, False, False, False, False, False],
    facetSatisfied=[True, True, True, True, False, True, True, True, True, True, True, True],
    facetWidths=[0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], facetValues=[0, 1],
    factHasDep=[True, True], factDepWidths=[1, 1], factDepItems=[1, 3], conflictHasDep=True, conflictLeaves=[1, 3, 0],
    wordWidths=[1, 2, 1], wordChars=[97, 98, 98, 98], langWidths=[2, 2, 1, 1], langWords=[0, 1, 2, 1, 0, 2],
    backgroundAny=False, backgroundLengths=[1, 2], guessPresent=True, guessLength=1, guessLeaf=0, proofPositions=[0, 1],
    store=[0, 1], coreWidths=[], coreIds=[], coreWatch=[], bucketWidths=[], bucketItems=[])
p21_off = copy.deepcopy(p21_main)
p21_off['enabled'] = False
p21_gate = copy.deepcopy(p21_main)
p21_gate['facetSatisfied'][8] = False
p21_valid = copy.deepcopy(p21_main)
p21_valid.update(facetValues=[2, 3], conflictLeaves=[1, 3], backgroundAny=True, backgroundLengths=[],
    guessPresent=False, guessLength=0, store=[0, 1, 2, 3], coreWidths=[2], coreIds=[2, 3], coreWatch=[0], bucketWidths=[0, 0, 1], bucketItems=[0])
p21_empty = copy.deepcopy(p21_main)
p21_empty.update(facetWidths=[0]*12, facetValues=[], factHasDep=[], factDepWidths=[], factDepItems=[],
    conflictHasDep=False, conflictLeaves=[], proofPositions=[], guessPresent=False, guessLength=0, store=[], backgroundAny=True, backgroundLengths=[])
p21 = dict(id='P21', coverage_candidate='C12-length-conditional-core-sufficiency', path='src/util/stx_search_tree.h',
    entry='cache_insert', entry_needle='void cache_insert(node const& n)', entry_name='CacheInsertEntry',
    quote_needle='// facts that could have contributed to THIS conflict (see', inputs=p21_inputs,
    outputs=dict(inserted='bool', storeOut='seq<int>', coreWidthsOut='seq<int>', coreIdsOut='seq<int>', coreWatchOut='seq<int>', bucketWidthsOut='seq<int>', bucketItemsOut='seq<int>'),
    representation=[
        'Facet rows contain all active plain membership syntax descriptors in this focused family. Descriptor equality is integer identity, not extensional language equality; distinct descriptors may accept the same finite words.',
        'Each language is an explicit list of word IDs; each word is a flattened character sequence. These are exact finite-language semantics, not an arbitrary unsat oracle or a guessed truth table.',
        'Dependency leaf vectors represent sets as observed by contains/linearize; duplicates allowed. Null handles are distinct from nonnull empty-leaf handles.',
        'The canonical store is an ordered unique descriptor vector. Core and watch-bucket rows are flattened with widths; coreWatch stores literal positions, not descriptor IDs.',
        'The fixed per-solve background permits any nonnegative length or an explicit finite length set. A temporary exact-length witness query is a separate premise, never silently included in fixed background.',
        'proofPositions are observed participating fact positions, not returned solver verdicts; their finite-language contradiction is independently recomputed by a body-defined predicate.',
    ],
    domain=[
        domain('All flattened partitions, facet arrays, dependency arrays, descriptor IDs, word IDs, core IDs and bucket references are well-formed; only contributing facet rows supply signature facts; observed noncontributing rows are empty in this family.', 'Faithful focused membership-family embedding of compute_constraints/append_constraints; excludes no member of the concrete candidate. Not a complete model of other theory constraint semantics.'),
        domain('Store descriptors are unique; every old core is nonempty with a valid watch position; every core occurs exactly once in the watch bucket for its watched descriptor; absent trailing buckets are allowed.', 'Canonical intern and watch-list state invariant, without assuming semantic unsatisfiability of old cores.'),
        domain('All source ID/count fields and maximum append sizes fit unsigned32; characters are valid code points; dependency leaves are unsigned32; background lengths are nonnegative.', 'Representation and successful vector growth. No tiny word/collection cap or unproved overflow exclusion beyond machine representation.'),
        domain('When enabled, eligible and the filtered signature is nonempty, proofPositions designate collected contributing facts and their dependencies are contained in the nonnull conflict union (or unconditional when conflict is null); a present temporary guess has its conditional leaf in that union.', 'Observed provenance of the inspected closure: actual participating membership handles and optional model-length handle are joined. This does not assume the cached set itself is contradictory.'),
        domain('Under that same ready-to-insert guard, the body-defined fixed-background plus proof-position language constraints plus optional guessed length have empty intersection. If a length guess is present it is nonnegative, permitted by fixed background, and each signature language separately admits that model length.', 'Independently checkable finite-language closing certificate and minimally consistent model observation, not an assumed unsat-core oracle. The joint original languages may still intersect at another length.'),
    ],
    whole_positive_property='CacheStateWellFormed(out) && CacheInsertExact(in,out) && (AllCoresUnsat(in,FixedBackground) ==> AllCoresUnsat(out,FixedBackground))',
    positive_meaning='The whole insertion preserves structural/canonical/watch state and the semantic contradiction invariant of the entire cache under the fixed per-solve background. Temporary query guesses are not part of that background.',
    computation=[
        'Return unchanged if cache disabled or any noncontributing facet reports not satisfied. Collect contributing facet facts in facet/row order; return unchanged if empty.',
        'If conflict is null retain all facts. Otherwise retain each null-dependency fact and each fact whose every dependency leaf belongs to the conflict union. Return unchanged if this list is empty.',
        'Intern every retained value in order, preserving prior canonical IDs and appending genuinely absent descriptor values. Repeated IDs in a core remain repeated.',
        'Append exactly one core with the complete retained ID vector and watch position0. Watch its first ID: grow bucket vector only as needed and append the new core index to that bucket, preserving every old core/store/watch row.',
        'Expose inserted as the observed core-count increment; do not model lookup/rewatch here or assume its converse contract.',
    ],
    required_helpers=[
        helper('FiniteLanguageAccepts/JointSatisfiable', 'Body-defined membership in explicit character words and complete finite-language intersection under fixed background and optional query length. For zero language facts, existence depends only on whether background permits a length.', 'seq_mem_facet.cpp:886-913; seq_mem_facet.h:65-94'),
        helper('ClosingCertificate', 'Recompute the proof-position language intersection and conditional-length contradiction, including all leaf-inclusion checks; no abstract boolean oracle.', 'seq_mem_facet.cpp:898-912; dependency.h:196-275'),
        helper('Collect/Filter/Intern/Watch', 'Body-defined facet traversal, actual null/subset rules, canonical descriptor insertion, and complete bucket resize/append effects.', 'stx_search_tree.h:600-610,630-659,775-847'),
        helper('CacheInsertExact', 'Full logical transition relation: exact early returns, ordered retained IDs and newly interned values, complete appended core/watch state and frame for all prior state.', 'stx_search_tree.h:821-847'),
    ],
    examples=[example('temporary-length-premise', p21_main, 'Languages {a,bb} and {b,bb}; query length1; fixed background allows1,2. No claimed verdict until Dafny checks.'),
              example('disabled-cache', p21_off, 'Identical semantic context but insertion disabled.'),
              example('excluded-live-request', p21_gate, 'Noncontributing request facet rejects eligibility; backend observation remains SAT.'),
              example('unconditional-contradiction-existing-watch', p21_valid, 'Languages {a} and {b}; valid old core and existing watched bucket; append without a temporary premise.'),
              example('empty-signature', p21_empty, 'No contributing facts; no closing certificate needed on the no-insertion path.')],
    limitations=['Finite-language, one-sequence-variable semantics; arbitrary regexes and other constraint kinds are not translated.',
                 'Full native producer reachability, earlier template/monadic processing, actual arithmetic model choice, helper core completeness and later cache hits remain unproved.',
                 'P19 clone/live-pointer mismatch may suppress hits; model refutation would concern stored-core sufficiency, not an observed wrong UNSAT result.',
                 'Certificate is required only on a ready-to-insert path; bypass examples exercise the entry but do not claim a native closing-node construction.'])

p22_inputs = dict(query='int', owned='seq<int>', heapValues='seq<int>', heapHashes='seq<int>', heapIds='seq<int>')
p22 = dict(id='P22', coverage_candidate='C12-canonical-storage-positive-comparison', path='src/util/stx_search_tree.h',
    entry='constraint_store::intern', entry_needle='unsigned intern(constraint_i const& c)', entry_name='CanonicalInternEntry',
    quote_needle='constraint_i* owned = c.clone();', inputs=p22_inputs,
    outputs=dict(id='int', ownedOut='seq<int>', valuesOut='seq<int>', hashesOut='seq<int>', idsOut='seq<int>'),
    domain=[
        domain('Heap columns have equal length, query and owned pointers are valid arena indices, owned pointers are distinct and their descriptor values are unique, and each owned object stores its canonical vector index.', 'Owned clone vector and canonical table representation; borrowed live query may alias an owner or be a distinct equal object.'),
        domain('Hash values are unsigned64 and equal descriptor values have equal low32 hash bits; object ID fields are unsigned32; old owned size plus1 is below2^32.', 'Actual ptr_hash truncates hash() to unsigned; compatible hash/equals and canonical unsigned IDs, with successful allocation.'),
    ],
    whole_positive_property='CanonicalStoreWellFormed(out) && InternTransitionExact(in,out) && CanonicalClassPreserved(in,out,id)',
    positive_meaning='Return the unique canonical ID of the query value; hit changes no heap/store state. Miss owns a fresh equal-value/hash clone, assigns exactly the old store size as its ID, appends it once, and preserves every prior object and canonical identity.',
    computation=[
        'Body-defined Find scans the represented canonical owners using low32 hash equality and semantic descriptor equality; no convenient found flag is accepted as input.',
        'On hit return its stored canonical ID with every output state unchanged.',
        'On miss Clone allocates a fresh arena index, copies value/hash, initializes store_id=UINT_MAX as constraint_i does, then set_store_id assigns old owned size; append clone to owned and canonical membership.',
        'The hashtable is modeled by its valid canonical membership ADT, not native bucket placement, allocator addresses or timing. Preserve collisions and physical query aliases.',
    ],
    required_helpers=[
        helper('FindByHashAndValue', 'Body-defined lookup over unique canonical owners; low32 collisions require equals, not hash equality alone.', 'stx_search_tree.h:579-599'),
        helper('CloneAndAssignId', 'Body-defined successful clone of all modeled value/hash fields, fresh arena identity, UINT_MAX initialization and explicit new canonical ID assignment.', 'stx_search_tree.h:122-132,603-609; seq_eq_facet.h:152'),
        helper('InternTransitionExact/CanonicalClassPreserved', 'Body-defined hit/miss state, ownership, complete old heap prefix, exact query equivalence class and first canonical ID relation.', 'stx_search_tree.h:600-610'),
    ],
    examples=[example('first-intern', dict(query=0, owned=[], heapValues=[7], heapHashes=[42], heapIds=[4294967295]), 'Allocate and own first canonical clone.'),
              example('alias-hit', dict(query=1, owned=[0], heapValues=[7,7], heapHashes=[42,42], heapIds=[0,4294967295]), 'Borrowed live pointer differs from the equal canonical owner.'),
              example('hash-collision-miss', dict(query=1, owned=[0], heapValues=[7,8], heapHashes=[4294967297,1], heapIds=[0,4294967295]), 'Different values collide after actual unsigned32 hash truncation.'),
              example('canonical-pointer-hit', dict(query=0, owned=[0], heapValues=[7], heapHashes=[42], heapIds=[0]), 'Identity fast path agrees with semantic lookup.')],
    limitations=['Semantic descriptor/hash projection plus successful clone/membership ADT, not C++ allocator/hashtable equivalence.',
                 'No proof that canonical storage suffices for semantic unsat cores or repairs P19 rewatch; this is a distinct complete entry contract.'])

properties = [p20, p21, p22]
assert len(properties) == 3 and len({p['entry'] for p in properties}) == 3
for prop in properties:
    assert prop['domain'] and all(d['origin']=='inferred' and d['optional'] is False for d in prop['domain'])
    assert prop['required_helpers'] and all(h['body_required'] for h in prop['required_helpers'])
    assert len(prop['examples']) >= 3
    for ex in prop['examples']:
        assert set(ex['inputs']) == set(prop['inputs']), (prop['id'], ex['label'])
        for key, typ in prop['inputs'].items():
            value = ex['inputs'][key]
            assert (type(value) is int if typ=='int' else type(value) is bool if typ=='bool' else
                    type(value) is list and all(type(v) is (int if typ=='seq<int>' else bool) for v in value)), (prop['id'], key)

prior_entries = []
for name in ['nfv2-selection.json','nfv3-selection.json']:
    prior_entries.extend(p['entry'] for p in json.loads((ROOT/name).read_text())['properties'])
assert not set(prior_entries) & {p['entry'] for p in properties}

paths = sorted({p['path'] for p in properties} | {'src/ast/seq/seq_power_facet.h'})
listing = subprocess.check_output(['git','ls-tree',PIN,'--',*paths], cwd=REPO, text=True)
oids = {line.split('\t',1)[1]:line.split()[2] for line in listing.splitlines()}
assert set(oids) == set(paths)
raw = subprocess.check_output(['git','cat-file','--batch'], input=('\n'.join(oids[p] for p in paths)+'\n').encode(), cwd=REPO)
offset=0
texts={}
file_records=[]
for path in paths:
    end=raw.index(b'\n',offset)
    oid,kind,size=raw[offset:end].decode().split()
    blob=raw[end+1:end+1+int(size)]
    offset=end+2+int(size)
    assert kind=='blob' and oid==oids[path]
    assert hashlib.sha1(b'blob '+str(len(blob)).encode()+b'\0'+blob).hexdigest()==oid
    text=blob.decode()
    assert REPO.joinpath(*path.split('/')).read_text(encoding='utf-8') == text.replace('\r\n','\n')
    texts[path]=text
    file_records.append(dict(path=path,blob=oid,sha256=sha(blob)))
assert offset==len(raw)
diff=subprocess.check_output(['git','diff','--no-ext-diff','--unified=0',BASE,PIN,'--',*paths],cwd=REPO,text=True)
added={}
current=None
for line in diff.splitlines():
    if line.startswith('+++ b/'):
        current=line[6:]
    elif line.startswith('@@'):
        m=re.search(r'\+(\d+)(?:,(\d+))? @@',line)
        first=int(m[1]); count=int(m[2] or 1)
        added.setdefault(current,set()).update(range(first,first+count))
for prop in properties:
    text=texts[prop['path']]
    needle=prop.pop('entry_needle')
    assert text.count(needle)==1
    pos=text.index(needle)
    first=text.count('\n',0,pos)+1
    mask=re.sub(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"', lambda m: ''.join('\n' if c=='\n' else ' ' for c in m.group()),text,flags=re.S)
    opening=mask.index('{',pos); depth=1; lastpos=opening+1
    while depth:
        depth+=(mask[lastpos]=='{')-(mask[lastpos]=='}'); lastpos+=1
    last=text.count('\n',0,lastpos)+1
    prop['span']=[first,last]
    quote=prop.pop('quote_needle')
    matches=[(i,line) for i,line in enumerate(text.splitlines(),1) if first<=i<=last and quote in line]
    assert len(matches)==1
    prop['quote_line'],prop['grounding_quote']=matches[0]
    prop['changed_line_overlap']=sorted(added[prop['path']] & set(range(first,last+1)))
    assert prop['changed_line_overlap']
    prop['intent_origin']='source-inferred whole-entry hypothesis; no PR claim and no outcome'
    prop['exact_entry_source']=[dict(line=i,text=line) for i,line in enumerate(text.splitlines(),1) if first<=i<=last]

source_sha=emit('nfv4-selection-source-inventory.json',dict(head=PIN,merge_base=BASE,files=file_records,
    scopes=[dict(id=p['id'],path=p['path'],span=p['span'],quote_line=p['quote_line'],entry_source=p['exact_entry_source']) for p in properties],
    str_power_constructor_source=[dict(line=i,text=line) for i,line in enumerate(texts['src/ast/seq/seq_power_facet.h'].splitlines(),1) if 38<=i<=61]))
for prop in properties:
    del prop['exact_entry_source']
selection=dict(batch=4,head=PIN,master=MASTER,merge_base=BASE,
    nfv_upstream='599726579274cfeb1c0915414b911371527a9870',previous_publication='13cfdf0d3f046886dd16ae6aef2c9853679b4877',
    scope='Three selected distinct changed entries, frozen before Dafny modeling. Source-inferred hypotheses, not outcomes or native findings.',
    source_handoffs=handoffs,selection_source_sha256=source_sha,properties=properties,
    audit_protocol=['One complete positive conjunction per entry; do not split branches/conjuncts into more properties.',
        'All helpers have bodies and exact source/observed-input metadata; no assume, axioms, bodyless oracle, verifier attributes or admitted correspondence.',
        'Property-free validity and independent concrete domains precede each frozen whole positive check. Every refutation pins every input and mechanically negates the entire original conjunction.',
        'No optional restrictions selected; removal stage must record none rather than inventing a weakened goal. A shorter consequence must leave inputs AND outputs free and be independently refuted.',
        'Only entry computation may change for any candidate model repair; input/helper contracts and entire original goals stay fixed.',
        'Current source/tag/span validation is local provenance, not full upstream extractor/parser/admission or native translation equivalence.'],
    deferred=['Native driver reachability and later result/crash implications of all conditional candidates.',
        'General semantic cache soundness for arbitrary regexes, other constraint kinds and all excluded mutable state.',
        'Universal eq_facet elimination termination without an independently established producer invariant.',
        'P13 request queue and P18 complete word identity remain open; no weaker replacement or repeated identical proof run.'],
    models_created=False,verifier_attempts=0,native_executions=0)
selection_sha=emit('nfv4-selection.json',selection)
report_sha=sha((ROOT/'nfv4-selection.md').read_bytes())
freeze_sha=emit('nfv4-selection-freeze.json',dict(status='frozen_before_modeling',selection_sha256=selection_sha,
    selection_source_sha256=source_sha,report_sha256=report_sha,source_handoffs=handoffs,
    property_ids=[p['id'] for p in properties],entry_count=3,whole_property_count=3,
    concrete_example_count=sum(len(p['examples']) for p in properties),next_stage='nfv4-model',schedule_id=2,stop_schedule=False))
print(json.dumps(dict(status='pass',selected=[dict(id=p['id'],entry=p['entry'],span=p['span'],examples=len(p['examples']),inputs=len(p['inputs'])) for p in properties],
    selection_sha256=selection_sha,selection_source_sha256=source_sha,report_sha256=report_sha,freeze_sha256=freeze_sha,
    verifier_attempts=0,models_created=False),indent=2))
