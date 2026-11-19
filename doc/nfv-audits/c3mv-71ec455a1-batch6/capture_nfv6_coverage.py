"""Capture source-only candidate evidence with exact pinned Git blob provenance."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).parent
REPO=Path(r'C:\z3seq')
PIN='71ec455a18702fe695d0c924a535ff9f385bd58d'
BASE='437536cd64a544a1c329fc57d83e56e294fdf47c'
MASTER='bcad05a7bf7dd9b82bd7a665018e0480e737264b'
SPANS={
    'src/ast/seq/seq_stoi_facet.h':[(1,181)],
    'src/smt/theory_nseq.cpp':[(33,151),(172,195),(249,278),(310,338),(570,654),(727,738),(846,1002),(1067,1154),(1176,1185),(1428,1434)],
    'src/ast/simplifiers/seq_regular_simplifier.cpp':[(84,169),(245,358),(397,438),(518,540),(1149,1170),(1750,1838)],
    'src/ast/seq_decl_plugin.cpp':[(1040,1056),(1086,1116)],
    'src/util/util.cpp':[(70,80)],
    'src/smt/seq_nseq_ambient_context.h':[(24,73)],
    'src/smt/seq_axioms.cpp':[(29,104)],
    'src/smt/seq_axioms.h':[(30,103)],
    'src/ast/seq/seq_axioms.cpp':[(835,988)],
    'src/ast/rewriter/seq_rewriter.cpp':[(879,925)],
    'src/util/trail.h':[(121,136),(209,223)],
    'src/smt/smt_model_generator.cpp':[(300,382)]}


def git(*args):
    return subprocess.check_output(['git','--no-pager',*args],cwd=REPO)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


assert not (ROOT/'nfv6-coverage-source-inventory.json').exists()
assert git('branch','--show-current').strip()==b'c3mv'
assert git('rev-parse','HEAD').strip()==b'4be813a75bdc59574df23da8ce5805a262171ba9'
assert git('rev-parse','HEAD:src').strip()==git('rev-parse',PIN+':src').strip()
assert not git('status','--porcelain=v1','-uall')
assert git('rev-parse','refs/stash').strip()==b'7af7fad70e9cea38601c67ff00d89f6b5576c2d6'
entries={}
for row in git('ls-tree','-r','-z',PIN,'--',*SPANS).split(b'\0'):
    if row:
        meta,name=row.split(b'\t',1)
        entries[name.decode()]=meta.split()[2]
assert set(entries)==set(SPANS)
names=sorted(entries)
raw=subprocess.run(['git','cat-file','--batch'],cwd=REPO,input=b''.join(entries[n]+b'\n' for n in names),stdout=subprocess.PIPE,check=True).stdout
offset=0
files=[]
texts={}
for name in names:
    end=raw.index(b'\n',offset)
    oid,kind,size=raw[offset:end].split()
    assert oid==entries[name] and kind==b'blob'
    size=int(size)
    content=raw[end+1:end+1+size]
    offset=end+2+size
    assert hashlib.sha1(b'blob '+str(size).encode()+b'\0'+content).hexdigest()==oid.decode()
    text=content.decode('utf-8')
    assert REPO.joinpath(*name.split('/')).read_text(encoding='utf-8')==text.replace('\r\n','\n')
    lines=text.splitlines()
    wanted=set()
    for lo,hi in SPANS[name]:
        assert 1<=lo<=hi<=len(lines),(name,lo,hi,len(lines))
        wanted.update(range(lo,hi+1))
    texts[name]=lines
    files.append(dict(path=name,blob=oid.decode(),sha256=hashlib.sha256(content).hexdigest(),
        spans=SPANS[name],excerpts=[dict(line=i,text=lines[i-1]) for i in sorted(wanted)]))
assert offset==len(raw)
candidates=[
    dict(id='C05-coherence-callbacks',path='src/ast/seq/seq_stoi_facet.h',entry='stoi_facet::check_stoi_coherence',span=[95,164],
        status='defer unconditional termination/native-safety claim; conditional full-state property possible only with disclosed callback frame and finite append trace',
        whole_property='Complete guard selection, saved term/depth identity, instantiation and guarded upper-bound event log, indexed/trail depth update, live-size iteration and progress return agree with actual processing order.',
        guards=['Early mode bounds>1 require bound<=2 and equal available arithmetic bounds.',
            'Current conversion=-1 skips; lengths use syntactic bound<=1 or early bound2,otherwise current unsigned length.',
            'Zero length and prev_k>=k skip; update occurs after BOTH callback/axiom events.'],
        environment=['Constructor binds callback to real positional axioms; ambient add_axiom reuses clause path.',
            'Callbacks may internalize/enqueue terms. Only explicit add_term is append-only,with pop trail; set_depth uses indexed value trail.',
            'No proved uniform bound on callback append growth/reentrancy/backtracking during this call; do not assume safety as the theorem.'],
        limitations=['No native crash or infinite-loop witness. Copied pair avoids one stale-reference pattern only.','Finite callback script must be body-defined and explicitly conditional,not arbitrary fuel masking a loop.']),
    dict(id='C13-nested-model-slots',path='src/smt/theory_nseq.cpp',entry='theory_nseq::seq_model_value_proc::mk_value',span=[89,151],
        status='conditional full consumer/producer-normal-return property candidate; no selection yet',
        whole_property='Given slots justified by the actual finite normally returning producer,consume each dependency once in order,maintain matched saved-prefix/exponent frames,and return the complete interpreted concatenation with nested powers and constant-run flushing preserved.',
        producer_span=[869,1002],
        evidence=['Positive integral powers emit begin,recursive base tokens,end; nonpositive powers emit empty.',
            'Every dependency append emits one slot and one enode; get_dependencies preserves order; model generator supplies one value per dependency.',
            'Begin/end flush character runs; end extracts suffix,shrinks to saved prefix,pops both stacks and re-adds rewritten power.'],
        limitations=['Paired control-flow is a normal-return structural observation,not proof that substitution recursion always terminates.',
            'Do not assume arbitrary slot balance and call it a native stack-safety proof; model finite producer structure or disclose the conditional grammar.',
            'Body-define word powers/token concatenation; abstract rewriter observations are not an assumed equivalence oracle.','Exclude no native sort/alias/lifetime concern silently; a string-only scope must be explicit.']),
    dict(id='C14-saturated-length',path='src/ast/simplifiers/seq_regular_simplifier.cpp',entry='regular_compiler::bounded_length',span=[138,169],
        status='ready for later whole-intent consideration,not selected',
        whole_property='On successful complete evaluation,the returned unsigned bound is UINT_MAX (unknown/saturated) or bounds actual interpreted string length for every admissible valuation; preserve exact extract/concat/ite/cache behavior.',
        requirements=['UINT_MAX is a sentinel,not an asserted numerical bound on unbounded mathematical lengths.',
            'add_truncate uses uint64 addition then saturates; no wraparound or blanket no-overflow precondition.',
            'Constant nonpositive extract count yields0; finite positive count intersects source bound; symbolic or out-of-unsigned count does not invent a finite cap.',
            'Ite uses max over both alternatives. Fallback max_length body must preserve empty/unit/at/literal/extract/concat/unknown cases.',
            'AST identity/cache/affine evaluation and depth>256,budget/cancellation behavior must be represented or explicitly scoped to normal return.'],
        limitations=['Not exact length inference,finite-bound completeness,all scalar arithmetic correctness,or proof of compiler/native integration.']),
    dict(id='C14-nonnegative-decimal-language',path='src/ast/simplifiers/seq_regular_simplifier.cpp',entry='regular_compiler::decimal_language with decimal_greater helper',span=[316,358],
        helper_span=[287,315],status='ready for later whole-intent consideration,not selected; distinct from P9 negative-threshold scope',
        whole_property='For nonnegative integral threshold and every word,membership in the complete constructed language agrees with its SMT stoi comparison for all6operators,including arbitrary leading zeros and invalid/empty words.',
        requirements=['Use canonical body-defined decimal rendering of integer bound; preserve 4096-digit budget and all tick failures as appropriate.',
            'decimal_greater builds right-to-left exact-prefix and higher-digit alternatives with shared arbitrary-digit suffixes,plus longer canonical positive words,then leading zero star.',
            'Equality/inequality use zero-star concatenated with canonical numeral,including one-or-more zeros for bound0.',
            'GE0 uses valid digit-plus; LT0 its complement; positive GE/LT use bound-1; LE/LT complement the constructed greater language.',
            'Complement ranges over all strings; invalid conversion=-1 is not an arbitrary negative input value.',
            'Regex constructors,membership and numeric word interpretation need bodies,not a convenient direct-comparison oracle.'],
        limitations=['One full semantic family,not six counted operator properties or a separate helper property to pad coverage.','No proof of native regex AST correspondence or transactional compiler correctness.'])]
for c in candidates:
    diff=git('diff','--no-ext-diff','--unified=0',BASE,PIN,'--',c['path']).decode()
    hunks=[]
    for a,n in re.findall(r'^@@ .*?\+(\d+)(?:,(\d+))? @@',diff,re.M):
        first=int(a); count=int(n) if n else 1
        if count:hunks.append([first,first+count-1])
    lo,hi=c['span']
    assert any(lo<=b and a<=hi for a,b in hunks)
    assert all(any(a<=line<=b for a,b in SPANS[c['path']]) for line in range(lo,hi+1))
    c['changed_hunks']=hunks
    c['eligibility']='Entry span intersects branch-introduced change; not a new upstream-master entry'
inventory=dict(head=PIN,master=MASTER,merge_base=BASE,files=files,source_execution=False)
path=ROOT/'nfv6-coverage-source-inventory.json'
path.write_text(json.dumps(inventory,indent=2)+'\n',encoding='utf-8',newline='\n')
ledger=dict(stage='nfv6-coverage',recorded_utc=datetime.now(timezone.utc).isoformat(),head=PIN,master=MASTER,merge_base=BASE,
    source_inventory_sha256=sha(path),candidates=candidates,selected_properties=0,verifier_invocations=0,native_executions=0,
    preserved_open_intents=['P13','P18','P20','P21','P22'],next_stage='nfv6-select',schedule_id=2,stop_schedule=False)
(ROOT/'nfv6-coverage-ledger.json').write_text(json.dumps(ledger,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='captured source-only',files=len(files),excerpt_lines=sum(len(f['excerpts']) for f in files),
    candidate_scopes=len(candidates),selected_properties=0,inventory_sha256=sha(path),ledger_sha256=sha(ROOT/'nfv6-coverage-ledger.json')),indent=2))
