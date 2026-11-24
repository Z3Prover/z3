import { createHash } from 'node:crypto';
import { constants } from 'node:fs';
import { lstat, mkdtemp, open, readdir, realpath, rm } from 'node:fs/promises';
import { basename, dirname, join } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { certify, type Request } from './certification.ts';
import type { Claim } from './claims.ts';
import { atomicJson, check, digest, emptyBlock, oid, parts, Publisher, type Binding, type Parent } from './publication.ts';
import { current, StateConflict, type LocalResult, type Paths } from './state.ts';

const corpusPin = '91c60596fd6a43de189a1ccba8080a3b48797537';
const sha256 = (s: unknown): s is string => typeof s === 'string' && /^[0-9a-f]{64}$/.test(s);
const runDir = (p: Paths, n: number) => join(p.state, 'runs', String(n));
const journal = (p: Paths, n: number, name: 'request'|'intent'|'receipt') => join(runDir(p,n), 'publication', `${name}.json`);
const exists = (path: string) => lstat(path).then(() => true, (e: NodeJS.ErrnoException) => { if (e.code !== 'ENOENT') throw e; return false; });
const publicRef = (n: number, c: string) => `refs/pulse/public/${n}/${oid(c)}`;
const privateRef = (n: number) => `refs/pulse/private/${n}`;
const parentRef = (h: string, m: string) => `refs/pulse/parents/${oid(h)}/${oid(m)}`;
const reqDigest = (r: Request) => digest(JSON.stringify([r.pr,r.iteration,r.H,r.M,r.P,r.privateCommit,r.tree,r.patchHash,r.itemId,r.beforeOut,r.beforeHash,r.afterHash,r.evaluator]));

type Verify = typeof certify;
export type Receipt = {
  version:1; pr:number; url:string; iteration:number; privateParent:string; privateTree:string; privateCommit:string;
  publicParent:string; tree:string; publicCommit:string; expectedHead:string; upstream:string; checkedOfficial:string; checkedAt:string; movements:number;
  requestDigest:string; previousBlockDigest:string; blockDigest:string; evaluator:string; evidence:string; scope:string; corpus:string;
  beforeOut:string; afterOut:string; beforeHash:string; afterHash:string; claims:Claim[];
};
type Intent = Receipt & {parked?:true};

async function regular(path:string) {
  check(await realpath(path) === path, 'Unexpected symlink in private publication evidence');
  const fd = await open(path, constants.O_RDONLY | constants.O_NOFOLLOW | constants.O_NONBLOCK);
  try { const s = await fd.stat(); check(s.isFile() && s.uid === process.getuid!(), 'Expected operator-owned publication evidence'); return fd; }
  catch (e) { await fd.close(); throw e; }
}
async function bytes(path:string) { const fd = await regular(path); try { return await fd.readFile(); } finally { await fd.close(); } }
const json = async <T>(path:string):Promise<T> => JSON.parse((await bytes(path)).toString());
const safePath = (path:string) => typeof path === 'string' && !/[\x00-\x1f\x7f\\]/.test(path) && path.split('/').every(s => s && s!=='.' && s!=='..');

// Record seals the inventories; a matching inventory alone is not evidence if its artifacts were removed or changed.
async function inventory(dir:string, expected:string, signal?:AbortSignal) {
  const manifest = await bytes(join(dir,'evidence.json'));
  check(sha256(expected) && digest(manifest) === expected, 'Verification inventory digest mismatch');
  const table = JSON.parse(manifest.toString());
  check(table && typeof table==='object' && !Array.isArray(table) && Object.keys(table).length, 'Empty verification inventory');
  const buffer=Buffer.allocUnsafe(128*1024);
  for (const [name, hash] of Object.entries(table)) {
    signal?.throwIfAborted(); check(safePath(name) && sha256(hash), 'Invalid verification inventory row');
    const fd = await regular(join(dir,name)), h = createHash('sha256');
    try {
      for (;;) {
        signal?.throwIfAborted();
        const {bytesRead}=await fd.read(buffer,0,buffer.length,null);
        if(!bytesRead) break;
        h.update(buffer.subarray(0,bytesRead));
      }
    } finally { await fd.close(); }
    check(h.digest('hex') === hash, 'Retained verification artifact changed');
  }
}

function shape(r:Request, pub:Publisher, n:number, p:Paths) {
  check(r && r.pr === pub.pr && Number.isSafeInteger(n) && n>0 && r.iteration===n && r.itemId && typeof r.itemId==='string', 'Invalid publication request identity');
  for(const id of [r.H,r.M,r.P,r.privateCommit,r.tree]) oid(id);
  check([r.patchHash,r.evaluator,r.beforeHash,r.afterHash].every(sha256), 'Invalid publication evidence hashes');
  check(typeof r.beforeOut==='string' && dirname(r.beforeOut)===join(p.state,'baseline',r.P,r.evaluator) && /^attempt-[a-zA-Z0-9]+$/.test(basename(r.beforeOut)), 'Unbound baseline evidence directory');
}
async function guard(pub:Publisher,p:Paths,r:Request,signal?:AbortSignal) {
  const n = current(p); shape(r,pub,n,p);
  const run = runDir(p,n), result = await json<LocalResult>(join(run,'result.json'));
  check(isDeepStrictEqual(await json(journal(p,n,'request')),r), 'Publication request differs from the recorded verification');
  check(result.iteration===n && result.base===r.P && result.item===r.itemId && result.ok===true && result.ciPass===true && result.accepted_change===1 && result.commit===r.privateCommit && result.patch===join(run,'attempt.patch'), 'Not the accepted, green private result');
  const patch=await bytes(join(run,'attempt.patch'));
  check(patch.length && digest(patch)===r.patchHash && (await bytes(join(run,'attempt.sha256'))).toString()===`${r.patchHash}  attempt.patch\n`, 'Archived private patch changed');
  const git = (...args:string[]) => pub.text(args,p.worktree,signal);
  check(await git('symbolic-ref','HEAD')==='refs/heads/loop/pulse-local' && await git('rev-parse','HEAD')===r.privateCommit && !await git('status','--porcelain=v1','--untracked-files=all'), 'Private accepted ref or checkout changed');
  check(await git('show','-s','--format=%P',r.privateCommit)===r.P && await git('rev-parse',`${r.privateCommit}^{tree}`)===r.tree && await pub.text(['rev-parse','--verify',parentRef(r.H,r.M)])===r.P, 'Private parent/tree not the verified pair');
  check(patch.equals(await pub.git(['diff','--binary','--full-index','--no-ext-diff','--no-textconv',r.P,r.privateCommit,'--'],p.worktree,undefined,signal)), 'Private commit differs from captured patch');
  await inventory(r.beforeOut,r.beforeHash,signal); await inventory(join(run,'after'),r.afterHash,signal);
  return patch;
}

function checkClaims(rows:Claim[], prior:Claim[]) {
  check(Array.isArray(rows),'Missing certified claim rows');
  const seen = new Map<string,Claim>();
  for (const c of rows) {
    check(c && safePath(c.path), 'Invalid certified claim path');
    if(c.kind==='formula') check(/^regressions\/(proofs|smtlib-sample)\/.+\.smt2$/.test(c.path) && c.name===c.path && sha256(c.sha256) && c.key===`${corpusPin}:${c.path}:${c.sha256}`, 'Invalid certified formula identity');
    else check(c.kind==='lemma' && c.path.startsWith('fstar/') && c.path.endsWith('.fst') && /^[\p{L}_][\p{L}\p{N}_']*(?:\.[\p{L}_][\p{L}\p{N}_']*)+$/u.test(c.name) && typeof c.type==='string' && c.type.trim() && Number.isSafeInteger(c.line) && c.line! > 0 && c.key===`${c.name}:${digest(c.type)}`, 'Invalid checked lemma identity');
    check(!seen.has(c.key),'Duplicate certificate claim key'); seen.set(c.key,c);
  }
  check(prior.every(c=>seen.get(c.key)?.kind===c.kind), 'Earlier public claim no longer certified');
}
const pathURL = (s:string) => s.split('/').map(p=>encodeURIComponent(p).replace(/[!'()*]/g,c=>`%${c.charCodeAt(0).toString(16).toUpperCase()}`)).join('/');
const code = (s:string) => { const fence='`'.repeat(1+Math.max(0,...Array.from(s.matchAll(/`+/g),m=>m[0].length))); return fence.length===1 ? `\`${s}\`` : `${fence} ${s} ${fence}`; };
const sorted = (claims:Claim[]) => [...claims].sort((a,b)=>a.kind<b.kind?-1:a.kind>b.kind?1:a.key<b.key?-1:a.key>b.key?1:0);
function block(pub:Publisher,c:string,claims:Claim[],previous:string) {
  const links=`[PR #${pub.pr}](${pub.url}) · [verified update](${pub.url}/commits/${oid(c)})`;
  const rows=sorted(claims).map(q=>q.kind==='formula'
    ? `- The native checker certified the proof for ${code(q.path)}. [input](https://github.com/Z3Prover/z3test/blob/${corpusPin}/${pathURL(q.path)}) · ${links}`
    : `- F* checked ${code(q.name)} under its declared assumptions. [definition](https://github.com/elefthei/z3/blob/${c}/${pathURL(q.path)}#L${q.line}) · ${links}`);
  const text=rows.length?emptyBlock.replace('No formal claims published yet.',()=>rows.join('\n')):emptyBlock;
  return previous.includes('\r\n')?text.replaceAll('\n','\r\n'):text;
}
function bodyFor(body:string,previous:string,target:string,repair=false) {
  const {prefix,block:actual,suffix}=parts(body);
  check(actual===previous || (repair && actual===target), 'Published claims block was edited; refusing to overwrite it');
  const result=prefix+target+suffix;
  check(parts(result).block===target,'Claim text collides with managed block markers');
  check(result.length<=65_536 || [...result].length<=65_536,'Proposed PR body exceeds 65,536 characters');return result;
}
function message(x:Pick<Receipt,'iteration'|'url'|'publicParent'|'tree'|'upstream'|'scope'|'corpus'|'evaluator'|'evidence'|'claims'>) {
  const rows=sorted(x.claims);
  const rowHash=digest(JSON.stringify(rows.map(q=>q.kind==='formula'?[q.kind,q.key,q.path,q.sha256]:[q.kind,q.key,q.name,q.path,q.line,q.type])));
  const claims=rows.map(q=>q.kind==='formula'?`Certified formula: ${pathURL(q.path)} sha256:${q.sha256}`:`Checked F* lemma: ${q.name} type-sha256:${digest(q.type!)}`);
  return [`Pulse: apply verified checker change (iteration ${x.iteration})`, '', `PR: ${x.url}`, `Parent: ${x.publicParent}`, `Tree: ${x.tree}`, `Official master: ${x.upstream}`, 'Verifier: F* v2026.10.25, full OCaml checker and native tests', `Evaluator SHA-256: ${x.evaluator}`, `Scope SHA-256: ${x.scope}`, `Corpus: Z3Prover/z3test@${x.corpus}; 17 proofs + 225 SMT-LIB sample cases`, 'Outcome: selected improvement verified; green candidate build and 242/242 cases evaluated', `Evidence SHA-256: ${x.evidence}`, `Certified rows SHA-256: ${rowHash}`, ...claims].join('\n');
}
async function pin(pub:Publisher,ref:string,commit:string,signal?:AbortSignal) {
  const old=await pub.text(['for-each-ref','--format=%(objectname)',ref],pub.repo,signal);
  if(old) check(old===commit,'Immutable publication ref changed');
  else await pub.git(['update-ref',ref,commit,''],pub.repo,undefined,signal);
}
async function verifyCommit(pub:Publisher,t:Receipt,signal?:AbortSignal) {
  check(t.version===1 && t.pr===pub.pr && t.url===pub.url && Number.isSafeInteger(t.iteration) && t.iteration>0 && [0,1].includes(t.movements) && Number.isFinite(Date.parse(t.checkedAt)), 'Malformed publication journal');
  for(const id of [t.publicParent,t.tree,t.publicCommit,t.privateParent,t.privateTree,t.privateCommit,t.expectedHead,t.upstream,t.checkedOfficial]) oid(id);
  check(t.corpus===corpusPin && [t.requestDigest,t.previousBlockDigest,t.blockDigest,t.evaluator,t.evidence,t.scope,t.beforeHash,t.afterHash].every(sha256),'Invalid publication journal hashes');
  checkClaims(t.claims,[]);
  const proof=await pub.text(['show','-s','--format=%P%n%T%n%B',publicRef(t.iteration,t.publicCommit)],pub.repo,signal);
  check(proof===`${t.publicParent}\n${t.tree}\n${message(t)}` && await pub.text(['rev-parse','--verify',publicRef(t.iteration,t.publicCommit)])===t.publicCommit && await pub.text(['rev-parse','--verify',privateRef(t.iteration)])===t.privateCommit && await pub.text(['rev-parse','--verify',parentRef(t.expectedHead,t.upstream)])===t.publicParent, 'Publication journal does not match retained Git objects');
  check(await pub.text(['show','-s','--format=%P%n%T',t.privateCommit],pub.repo,signal)===`${t.privateParent}\n${t.privateTree}`,'Receipt private parent or tree differs from retained object');
}
async function acknowledged(pub:Publisher,p:Paths,b:Binding,signal?:AbortSignal) {
  if(!b.iteration) {check(b.block.replaceAll('\r\n','\n')===emptyBlock,'Bootstrap binding contains unacknowledged claims');return undefined;}
  const x=await json<Receipt>(journal(p,b.iteration,'receipt')); await verifyCommit(pub,x,signal);
  check(x.iteration===b.iteration && x.publicCommit===b.head && x.upstream===b.upstream && x.checkedOfficial===x.upstream && digest(b.block)===x.blockDigest && block(pub,x.publicCommit,x.claims,b.block)===b.block,'Acknowledged cursor differs from its receipt');return x;
}
function bindOutputs(p:Paths,r:Request,parent:Parent,before:string,after:string) {
  const run=runDir(p,r.iteration);
  if(before===r.beforeOut && after===join(run,'after')) {
    check(parent.P===r.P && parent.M===r.M,'Rebased evidence cannot reuse the original output pair');return;
  }
  const pair=dirname(before);
  check(typeof after==='string' && dirname(pair)===join(run,'publication') && /^pair-[a-zA-Z0-9]+$/.test(basename(pair)) && before===join(pair,'before') && after===join(pair,'after'), 'Verification output pair is outside this publication');
}
async function confirmIntent(pub:Publisher,p:Paths,b:Binding,r:Request,t:Intent,prior:Claim[],signal?:AbortSignal) {
  check(!t.parked && (t.checkedOfficial===t.upstream || t.movements===0),'Official master advanced again; publication is parked');
  await verifyCommit(pub,t,signal);
  check(t.iteration===r.iteration && t.requestDigest===reqDigest(r) && t.privateCommit===r.privateCommit && t.privateTree===r.tree && t.privateParent===r.P && t.expectedHead===r.H && b.head===r.H && b.iteration<r.iteration && t.previousBlockDigest===digest(b.block) && t.blockDigest===digest(block(pub,t.publicCommit,t.claims,b.block)) && t.movements===Number(t.upstream!==r.M),'Intent does not authorize this request and cursor');
  checkClaims(t.claims,prior);
  bindOutputs(p,r,{H:t.expectedHead,M:t.upstream,P:t.publicParent},t.beforeOut,t.afterOut);
  if(t.beforeOut!==r.beforeOut) {await inventory(t.beforeOut,t.beforeHash,signal); await inventory(t.afterOut,t.afterHash,signal);}
  else check(t.evaluator===r.evaluator && t.beforeHash===r.beforeHash && t.afterHash===r.afterHash,'Intent original evidence identity changed');
  check(t.evidence===digest(JSON.stringify({before:t.beforeHash,after:t.afterHash,claims:t.claims})), 'Intent certified evidence no longer matches');
}

// For a new parent there is no original tree OID to compare. Apply to a disposable index, not the publisher checkout.
async function portedTree(pub:Publisher,p:Paths,r:Request,parent:Parent,patch:Buffer,signal?:AbortSignal) {
  if(parent.P===r.P) return r.tree;
  const dir=await mkdtemp(join(runDir(p,r.iteration),'publication','index-'));
  try {
    await pub.git(['clone','-q','--shared','--no-checkout','--no-tags','--',pub.repo,dir],pub.repo,undefined,signal);
    await pub.git(['read-tree',parent.P],dir,undefined,signal); await pub.git(['apply','--cached','--binary','--whitespace=nowarn','-'],dir,patch,signal);
    return oid(await pub.text(['write-tree'],dir,signal));
  } finally { await rm(dir,{recursive:true,force:true}); }
}
async function finish(pub:Publisher,p:Paths,b:Binding,t:Receipt,signal?:AbortSignal) {
  const target=block(pub,t.publicCommit,t.claims,b.block), fresh=await pub.observed(signal);
  check(fresh.H===t.publicCommit,'Push not established at the bound fork and PR');
  check(current(p)===t.iteration && isDeepStrictEqual(await pub.binding(),b),'Publication cursor changed before body reconciliation');
  const pr=await pub.pull(signal);check(pr.head.sha===t.publicCommit,'PR head changed before body update');
  const body=bodyFor(pr.body,b.block,target,true), editing=body!==pr.body;
  if(editing) {
    // A lost PATCH response says nothing about the resulting body. Only the following GET can acknowledge it.
    try { await pub.pull(signal,body); } catch { signal?.throwIfAborted(); }
  }
  const after=await pub.observed(signal);
  check(after.H===t.publicCommit && (!editing || after.pr.body===body) && parts(after.pr.body).block===target,'Public head, description or claims update not confirmed; intent retained');
  const receiptPath=journal(p,t.iteration,'receipt');
  if(await exists(receiptPath)) check(isDeepStrictEqual(await json(receiptPath),t),'Conflicting existing publication receipt');
  else await atomicJson(receiptPath,t);
  check(isDeepStrictEqual(await pub.binding(),b),'Publication cursor changed before acknowledgement');
  await atomicJson(pub.bindingFile,{...b,head:t.publicCommit,upstream:t.upstream,block:target,iteration:t.iteration} satisfies Binding);
  return t;
}
async function transact(pub:Publisher,p:Paths,r:Request,resuming:boolean,signal:AbortSignal|undefined,verify:Verify):Promise<Receipt> {
  signal?.throwIfAborted();check(pub.repo===p.repo && pub.state===p.state && (verify===certify || pub.isFixture),'Unbound publisher or verifier');
  const b=await pub.binding(), patch=await guard(pub,p,r,signal), last=await acknowledged(pub,p,b,signal), prior=last?.claims??[];
  if(last && r.iteration===b.iteration) {
    check(last.requestDigest===reqDigest(r),'Wrong request for completed publication');const remote=await pub.observed(signal);
    check(remote.H===b.head && parts(remote.pr.body).block===b.block,'Completed publication no longer matches PR');return last;
  }
  check(r.iteration>b.iteration && r.H===b.head, 'Stale fork lease or publication iteration');
  const intentPath=journal(p,r.iteration,'intent');
  let previous:Intent|undefined=await exists(intentPath)?await json<Intent>(intentPath):undefined;
  check(!resuming || previous,'Missing Leader-authorized publication intent');
  if(previous) await confirmIntent(pub,p,b,r,previous,prior,signal);
  const receiptPath=journal(p,r.iteration,'receipt');
  const recorded=await exists(receiptPath); if(recorded) check(previous && isDeepStrictEqual(await json(receiptPath),previous),'Receipt without matching authorized intent');
  const remote=await pub.observed(signal);
  if(previous && remote.H===previous.publicCommit) {
    check(previous.checkedOfficial===previous.upstream && (!recorded || digest(parts(remote.pr.body).block)===previous.blockDigest),'Observed head or claims conflict with publication checkpoint');
    return finish(pub,p,b,previous,signal);
  }
  check(!recorded && remote.H===r.H && parts(remote.pr.body).block===b.block,'Unacknowledged head or managed PR block changed');
  await pub.git(['fetch','--no-tags','--no-recurse-submodules','--',p.worktree,r.privateCommit],pub.repo,undefined,signal);
  await pin(pub,privateRef(r.iteration),r.privateCommit,signal);
  let seen=previous?.checkedOfficial??r.M, movements=Number(seen!==r.M);
  // Retain each observed move across a crash; a second distinct move parks the same request.
  async function observeTrunk(m:string,at:string) {
    if(m===seen) return;
    if(previous) {
      previous.checkedOfficial=m;previous.checkedAt=at;
      if(movements) previous.parked=true;
      await atomicJson(intentPath,previous);
    }
    check(++movements<=1,'Official master advanced again during certification; publication parked');
    seen=m;
  }
  await observeTrunk(remote.M,remote.checkedAt);
  for (;;) {
    const parent=await pub.parent(r.H,signal);
    const preparedAt=new Date().toISOString();await observeTrunk(parent.M,preparedAt);
    if(parent.M!==r.M) await pub.git(['merge-base','--is-ancestor',r.M,parent.M],pub.repo,undefined,signal);
    const expected=await portedTree(pub,p,r,parent,patch,signal);
    check(expected!==await pub.text(['rev-parse',`${parent.P}^{tree}`]),'Verified patch is empty on rebased parent');
    const v=await verify(pub,p,r,parent,prior,signal);signal?.throwIfAborted();
    check(v.tree===expected && v.corpus===corpusPin && [v.evaluator,v.evidence,v.scope].every(sha256),'Verifier returned another tree or invalid attestation');
    checkClaims(v.claims,prior);
    const {beforeOut,afterOut}=v;bindOutputs(p,r,parent,beforeOut,afterOut);
    const beforeHash=beforeOut===r.beforeOut?r.beforeHash:digest(await bytes(join(beforeOut,'evidence.json'))), afterHash=beforeOut===r.beforeOut?r.afterHash:digest(await bytes(join(afterOut,'evidence.json')));
    if(beforeOut!==r.beforeOut) {await inventory(beforeOut,beforeHash,signal);await inventory(afterOut,afterHash,signal);}
    else check(v.evaluator===r.evaluator,'Original evaluation was not run with this verifier');
    check(v.evidence===digest(JSON.stringify({before:beforeHash,after:afterHash,claims:v.claims})), 'Verifier receipt differs from paired inventories and claim rows');
    const info={version:1 as const,pr:r.pr,url:pub.url,iteration:r.iteration,privateTree:r.tree,privateCommit:r.privateCommit,privateParent:r.P,publicParent:parent.P,tree:v.tree,expectedHead:r.H,upstream:parent.M,requestDigest:reqDigest(r),previousBlockDigest:digest(b.block),claims:v.claims,scope:v.scope,corpus:v.corpus,evaluator:v.evaluator,evidence:v.evidence,beforeOut,afterOut,beforeHash,afterHash,movements};
    const text=message(info), C=previous && message(previous)===text ? previous.publicCommit : oid((await pub.git(['commit-tree',v.tree,'-p',parent.P],pub.repo,`${text}\n`,signal)).toString().trim());
    check(C!==r.privateCommit && await pub.text(['show','-s','--format=%P%n%T%n%B',C])===`${parent.P}\n${v.tree}\n${text}`,'Public commit does not match certified parent, tree and receipt');
    await pin(pub,publicRef(r.iteration,C),C,signal);
    check(current(p)===r.iteration && isDeepStrictEqual(await pub.binding(),b) && isDeepStrictEqual(await json(journal(p,r.iteration,'request')),r),'Publication authority changed during verification');
    const target=block(pub,C,v.claims,b.block), pull=await pub.pull(signal);
    check(pull.head.sha===r.H,'Fork head changed before intent');bodyFor(pull.body,b.block,target);
    const intent:Intent={...info,publicCommit:C,blockDigest:digest(target),checkedOfficial:parent.M,checkedAt:preparedAt};
    await atomicJson(intentPath,intent);previous=intent;
    const final=await pub.observed(signal);check(final.H===r.H,'Fork lease changed before push');bodyFor(final.pr.body,b.block,target);
    if(final.M!==parent.M) {await observeTrunk(final.M,final.checkedAt);continue;}
    intent.checkedAt=final.checkedAt;await atomicJson(intentPath,intent);
    signal?.throwIfAborted();
    // A transport error may arrive after Git accepted the push. Never retry a push on that basis.
    try { await pub.push(C,r.H,signal); } catch { signal?.throwIfAborted(); }
    return finish(pub,p,b,intent,signal);
  }
}
function fail(error:unknown):never {
  if(error instanceof StateConflict || (error instanceof Error && error.name==='AbortError')) throw error;
  throw new StateConflict('Publication evidence or operation could not be confirmed; private state preserved',{cause:error});
}
export async function publish(pub:Publisher,p:Paths,r:Request,signal?:AbortSignal,verify:Verify=certify):Promise<Receipt> {
  try {return await transact(pub,p,r,false,signal,verify);} catch(e){fail(e);}
}
export async function reconcile(pub:Publisher,p:Paths,signal?:AbortSignal,verify:Verify=certify):Promise<void> {
  try {
    signal?.throwIfAborted();check(pub.repo===p.repo && pub.state===p.state && (verify===certify || pub.isFixture),'Unbound recovery publisher or verifier');
    const b=await pub.binding();await acknowledged(pub,p,b,signal);
    let n=0;
    if(!await exists(join(p.state,'iteration'))) check(!b.iteration && !(await readdir(p.state)).length,'Missing acknowledged campaign state');
    else n=current(p);
    check(n>=b.iteration,'Publication cursor ahead of private iteration');
    // Rejected/idle decisions need no receipts; no accepted private result may fall through this gap.
    for(let i=b.iteration+1;i<=n;i++) {
      const run=runDir(p,i);check(await realpath(run)===run,'Missing or foreign private iteration');
      check(!await exists(join(run,'.result.pending.json')),'Interrupted private decision before publication');
      const decision=join(run,'result.json'), requested=await exists(journal(p,i,'request')), authorized=await exists(journal(p,i,'intent')), completed=await exists(journal(p,i,'receipt'));
      if(!await exists(decision)) {check(!requested && !authorized && !completed && !await exists(join(run,'attempt.patch')),'Unfinished private verification or publication');continue;}
      const result=await json<LocalResult>(decision);
      check(result.iteration===i && typeof result.ok==='boolean' && result.ok===(result.commit!==null) && result.accepted_change===Number(result.ok),'Invalid archived publication decision');
      if(!result.ok) {check(!requested && !authorized && !completed,'Publication journal on rejected or idle private result');continue;}
      check(i===n && result.ciPass===true && requested && authorized,'Accepted private change lacks Leader authorization; preserve request and resume explicitly');
      await transact(pub,p,await json<Request>(journal(p,i,'request')),true,signal,verify);return;
    }
    const remote=await pub.observed(signal);check(remote.H===b.head && parts(remote.pr.body).block===b.block,'Observed fork or PR claims differ from acknowledged cursor');
  } catch(e){fail(e);}
}
