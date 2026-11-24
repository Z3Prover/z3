import { mkdir, mkdtemp, readFile, realpath } from 'node:fs/promises';
import { basename, dirname, join } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { analyze, evaluatorIdentity, judge, prCandidateFailure, refreshQueue, regress, validatePatch } from './evaluation.ts';
import { extractClaims, type Claim } from './claims.ts';
import { current, type Paths } from './state.ts';
import { Publisher, type Parent, atomicJson, check, digest, oid } from './publication.ts';
import type { Loop } from './wf.ts';

export type Request={pr:number;iteration:number;H:string;M:string;P:string;privateCommit:string;tree:string;patchHash:string;itemId:string;beforeOut:string;beforeHash:string;afterHash:string;evaluator:string};
const sha256=(s:string|undefined):s is string=>typeof s==='string' && /^[0-9a-f]{64}$/.test(s);
const corpus='91c60596fd6a43de189a1ccba8080a3b48797537';
const artifact=async(dir:string,file:string)=>{const path=join(dir,file);check(await realpath(path)===path,'Evidence path is not canonical');return readFile(path);};

/** Record may request a turn but cannot authorize public effects. No remote call here. */
export async function requestPublication(x:Loop,signal?:AbortSignal):Promise<Request>{
  const p=x.paths,pub=x.publisher,parent=x.parent,r=x.result,a=x.attempt,b=x.selected?.before,after=x.verification?.after;
  check(pub && parent && r && r.ok && r.ciPass && r.accepted_change===1 && r.commit && a && b && after && x.selected?.item && x.beforeOut,'Missing independently accepted change');
  const dir=join(p.state,'runs',String(x.iteration)),binding=await pub.binding();
  check(current(p)===x.iteration && x.iteration===r.iteration && r.iteration===a.iteration && pub.pr===binding.pr && binding.head===parent.H && p.reviewedUpstream===parent.M && r.base===parent.P && x.sha===parent.P && b.sha===a.base && a.base===after.sha && after.sha===r.base && x.selected.item.id===r.item,'Stale publication result');
  check(b.buildOk && prCandidateFailure(after)===null && a.tree===after.tree && sha256(b.evaluator) && after.evaluator===b.evaluator && sha256(b.evidenceSha256) && sha256(after.evidenceSha256),'Invalid candidate identity or incomplete evidence');
  check(a.patch===join(dir,'attempt.patch') && a.patch===r.patch && isDeepStrictEqual(JSON.parse((await artifact(dir,'result.json')).toString()),r),'Private decision is not the archived result');
  const bytes=await artifact(dir,'attempt.patch');check(bytes.length && digest(bytes)===a.hash && (await artifact(dir,'attempt.sha256')).toString()===`${a.hash}  attempt.patch\n`,'Patch archive digest mismatch');
  const rev=(...args:string[])=>pub.text(args,p.worktree,signal);
  check(await rev('symbolic-ref','HEAD')==='refs/heads/loop/pulse-local' && await rev('rev-parse','HEAD')===oid(r.commit) && await rev('show','-s','--format=%P',r.commit)===r.base && await rev('rev-parse',`${r.commit}^{tree}`)===a.tree && await rev('rev-parse',`${r.base}^{tree}`)===b.tree && !await rev('status','--porcelain','--untracked-files=all'),'Private commit, parent, index or tree changed');
  const exact=await pub.git(['diff','--binary','--full-index','--no-ext-diff','--no-textconv',r.base,r.commit,'--'],p.worktree,undefined,signal);
  check(exact.equals(bytes),'Private commit differs from independently verified patch');
  check(dirname(x.beforeOut)===join(p.state,'baseline',r.base,b.evaluator) && /^attempt-[A-Za-z0-9]+$/.test(basename(x.beforeOut)) && digest(await artifact(x.beforeOut,'evidence.json'))===b.evidenceSha256 && digest(await artifact(join(dir,'after'),'evidence.json'))===after.evidenceSha256,'Evidence manifest changed or outside run');
  const request={pr:pub.pr,iteration:r.iteration,...parent,privateCommit:r.commit,tree:a.tree,patchHash:a.hash,itemId:r.item,beforeOut:x.beforeOut,beforeHash:b.evidenceSha256,afterHash:after.evidenceSha256,evaluator:b.evaluator};
  const out=join(dir,'publication');await mkdir(out,{mode:0o700});await atomicJson(join(out,'request.json'),request);return Object.freeze(request);
}

export async function certify(pub:Publisher,p:Paths,r:Request,parent:Parent,prior:Claim[],signal?:AbortSignal){
  check(pub.pr===r.pr && parent.H===r.H && current(p)===r.iteration,'Certification is not bound to this iteration');
  const run=join(p.state,'runs',String(r.iteration));const patch=await artifact(run,'attempt.patch');check(patch.length && digest(patch)===r.patchHash,'Archived patch changed');
  const attempt=await mkdtemp(join(run,'publication','pair-'));
  const checkout=async(name:string)=>{const root=join(attempt,name);await mkdir(root,{mode:0o700});await pub.git(['init','-q','--template='],root);await pub.git(['fetch','--no-tags','--depth=1','--no-recurse-submodules','--',pub.repo,parent.P],root,undefined,signal);await pub.git(['switch','--detach','--no-overwrite-ignore',parent.P],root);return {...p,worktree:root,reviewedUpstream:parent.M};};
  const [left,right]=await Promise.all([checkout('parent'),checkout('candidate')]);
  await pub.git(['apply','--index','--binary','--whitespace=nowarn','-'],right.worktree,patch,signal);
  const tree=oid(await pub.text(['write-tree'],right.worktree));check(tree!==await pub.text(['rev-parse',`${parent.P}^{tree}`]),'Rebased candidate is empty');
  await validatePatch(right,parent.P,right.worktree);
  const identity=await evaluatorIdentity(left,signal);check(identity===await evaluatorIdentity(right,signal),'Baseline and candidate use different verifiers');
  const reuse=parent.P===r.P && parent.M===r.M && tree===r.tree && identity===r.evaluator;
  const beforeOut=reuse?r.beforeOut:join(attempt,'before'),afterOut=reuse?join(run,'after'):join(attempt,'after');
  if(!reuse){check(await regress(left,beforeOut,signal),'Rebased baseline did not build');check(await regress(right,afterOut,signal),'Rebased candidate did not build');}
  const before=await analyze(left,beforeOut,parent.P,signal),after=await analyze(right,afterOut,parent.P,signal);
  check(before.buildOk && before.sha===parent.P && after.sha===parent.P && before.tree===await pub.text(['rev-parse',`${parent.P}^{tree}`]) && after.tree===tree && before.evaluator===identity && after.evaluator===identity && sha256(before.evidenceSha256) && sha256(after.evidenceSha256),'Paired evidence has wrong parent, tree or evaluator');
  if(reuse)check(before.evidenceSha256===r.beforeHash && after.evidenceSha256===r.afterHash,'Original verification evidence no longer matches');
  const item=refreshQueue({items:[]},before).items.find(i=>i.id===r.itemId),failure=prCandidateFailure(after);
  check(!failure,failure??'Invalid candidate');check(item && judge(item,before,after).ok,'Verified work item obsolete or no longer an improvement');
  const claims=await extractClaims({p:right,parent:parent.P,tree,beforeOut,afterOut,before,after},prior,signal);
  const build=JSON.parse((await artifact(afterOut,'build.json')).toString());check(sha256(build.scope_sha256),'Missing full scope receipt');
  // Transfer the exact tested tree through a local commit; commit-tree in the publisher supplies the public identity.
  const proof=oid((await pub.git(['-c','user.name=Pulse verifier','-c','user.email=verifier@localhost','commit-tree',tree,'-p',parent.P,'-m','Tested tree'],right.worktree)).toString().trim());
  await pub.git(['fetch','--no-tags','--no-recurse-submodules','--',right.worktree,proof]);check(await pub.text(['rev-parse',`${proof}^{tree}`])===tree,'Certified tree transfer failed');
  return {tree,claims,beforeOut,afterOut,evaluator:identity,evidence:digest(JSON.stringify({before:before.evidenceSha256,after:after.evidenceSha256,claims})),scope:build.scope_sha256,corpus};
}
