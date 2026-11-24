import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdir, mkdtemp, readFile, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { publicationFixture } from './publication.check.ts';
import { acquire, adoptPrParent, capture, next, prepare, record, saveQueue, verificationPaths } from './state.ts';
import { digest, parts } from './publication.ts';
import { refreshQueue, validatePatch, type Analysis } from './evaluation.ts';
import { requestPublication, type certify } from './certification.ts';
import { publish, reconcile } from './transaction.ts';
import type { Claim } from './claims.ts';
import type { Loop } from './wf.ts';

const revision='91c60596fd6a43de189a1ccba8080a3b48797537';
const samples=[['regressions/proofs/canaries/array_axiom_log.smt2','2d0cd6240c1a63b63e9bbddaada3aaccc9d46ea968ca19c662f23ef04bd2b255'],['regressions/proofs/canaries/real_numeral_farkas.smt2','04aac3ca8838fdf5ba774552250bebfe7f4892482d6f835f67b6ed26431394e4']] as const;
async function evidence(dir:string,outcome:string){await mkdir(dir,{recursive:true,mode:0o700});await writeFile(join(dir,'outcome.txt'),outcome);const manifest=JSON.stringify({'outcome.txt':digest(outcome)});await writeFile(join(dir,'evidence.json'),manifest);return digest(manifest);}

/** Real protected tree, archive, state.record and leases; synthetic measured verdicts, never public evidence. */
export async function acceptedGraphFixture(){
  const f=await publicationFixture(true),binding=await f.pub.initialize(f.first),p={...f.p,base:binding.seed,reviewedUpstream:binding.upstream};
  const unlock=acquire(p);let step=0;const verified:string[]=[];
  const close=async()=>{unlock();execFileSync('/usr/bin/btrfs',['subvolume','delete',p.worktree],{stdio:'pipe'});await f.close();};
  const cycle=async(performance=false)=>{
    const b=await f.pub.binding(),parent=await f.pub.parent(b.head);p.reviewedUpstream=parent.M;let tip=await prepare(p);await adoptPrParent(p,tip,parent.P);tip=parent.P;
    const iteration=next(p),run=join(p.state,'runs',String(iteration));const evaluator=digest('fixture verifier:'+tip),beforeOut=join(p.state,'baseline',tip,evaluator,'attempt-Fixture');
    const [target,hash]=samples[step%2]!;const cases:Analysis['cases']={};for(let i=0;i<241;i++)cases[`fixture/${i}.smt2`]={outcome:'ACCEPT',wall:1};cases[target]={outcome:performance?'ACCEPT':'REJECT',wall:1,...(performance?{checkMs:100}:{stage:'stage=fixture'})};
    const before:Analysis={sha:tip,tree:f.git(p.worktree,'rev-parse','HEAD^{tree}'),evaluator,evidenceSha256:await evidence(beforeOut,JSON.stringify(cases)),ciPass:true,buildOk:true,tested:242,statsCases:0,counts:performance?{ACCEPT:242}:{REJECT:1,ACCEPT:241},cases,families:[],pending:0,proofNodes:0,checkMs:0,solveMs:0,lemmas:0,assumed:0};
    const queue=refreshQueue({items:[]},before),item=queue.items[0]!;saveQueue(p,queue);
    await writeFile(join(p.worktree,`src/pulse_fixture_${iteration}.cpp`),`int pulse_fixture_${iteration}() { return ${iteration}; }\n`);
    const a=await capture(p,iteration,tip);assert.ok(a);await verificationPaths(p,a);
    const afterCases={...cases,[target]:{outcome:'ACCEPT',wall:1,checkMs:30}};
    const after={...before,tree:a.tree,cases:afterCases,counts:{ACCEPT:242},evidenceSha256:await evidence(join(run,'after'),JSON.stringify(afterCases))};
    const report={text:'Title: fixture local change',stopReason:'stop'};
    const result=await record(p,{iteration,before,item,attempt:a,after,report});assert.ok(result.ok,result.reasons.join('; '));
    const context:Loop={paths:p,publisher:f.pub,sha:tip,iteration,parent,result,attempt:a,selected:{before,item},verification:{after,changed:true,report},beforeOut};step++;
    const verify:typeof certify=async(pub,pp,r,newParent,prior,signal)=>{
      verified.push(newParent.P);assert.equal(pub,f.pub);assert.equal(pp.state,p.state);assert.equal(r.tree,a.tree);
      // The fixture trunk can reverse the selected verdict. It must not get an old receipt.
      const root=await mkdtemp(join(f.dir,'paired-'));await pub.git(['init','-q','--template='],root);await pub.git(['fetch','--depth=1','--no-tags',pub.repo,newParent.P],root);await pub.git(['switch','--detach','FETCH_HEAD'],root);
      const patch=await readFile(a.patch);assert.equal(digest(patch),r.patchHash);await pub.git(['apply','--index','--binary','-'],root,patch,signal);await validatePatch({...pp,reviewedUpstream:newParent.M},newParent.P,root);
      assert.equal(await pub.text(['ls-files','--','deny-fixture'],root),'','paired candidate no longer qualifies');
      const tree=await pub.text(['write-tree'],root),tmp=f.git(root,'commit-tree',tree,'-p',newParent.P,'-m','Fixture tested candidate');await pub.git(['fetch','--no-tags',root,tmp]);
      const claim:Claim={kind:'formula',key:`${revision}:${target}:${hash}`,name:target,path:target,sha256:hash};const claims=performance?[...prior]:[...prior.filter(c=>c.key!==claim.key),claim];
      const changed=newParent.P!==r.P, pair=changed?await mkdtemp(join(run,'publication','pair-')):'';
      const left=changed?join(pair,'before'):beforeOut,right=changed?join(pair,'after'):join(run,'after');
      const hashes={before:changed?await evidence(left,`Baseline ${newParent.P}`):r.beforeHash,after:changed?await evidence(right,`Candidate ${tree}`):r.afterHash,claims};
      return {tree,claims,beforeOut:left,afterOut:right,evaluator:changed?digest('verified:'+newParent.P):r.evaluator,evidence:digest(JSON.stringify(hashes)),scope:digest('fixture scope'),corpus:revision};
    };
    return {context,result,verify};
  };
  try{return {...await cycle(),close,cycle,head:f.head,body:()=>f.data.body,f,verified};}catch(e){await close();throw e;}
}
export async function checkPublication(){
  const x=await acceptedGraphFixture(),{f}=x;try {
    const r=await requestPublication(x.context),i=f.head(),baseBody=f.data.body;
    await assert.rejects(reconcile(f.pub,x.context.paths,undefined,x.verify));assert.equal(f.head(),i);assert.equal(f.calls.writes,0);
    const bad={...r,tree:'0'.repeat(40)};await assert.rejects(publish(f.pub,x.context.paths,bad,undefined,x.verify));assert.equal(f.head(),i);assert.equal(f.calls.writes,0);
    f.data.state='closed';await assert.rejects(publish(f.pub,x.context.paths,r,undefined,x.verify));f.data.state='open';assert.equal(f.head(),i);assert.equal(f.calls.writes,0);
    for(const invalid of [baseBody.replace('No formal claims published yet.','hand edit'),baseBody+parts(baseBody).block,'X'.repeat(65536)+baseBody]){
      f.data.body=invalid;await assert.rejects(publish(f.pub,x.context.paths,r,undefined,x.verify));assert.equal(f.head(),i);assert.equal(f.calls.writes,0);
    }
    f.data.body=baseBody;
    const receipt=await publish(f.pub,x.context.paths,r,undefined,x.verify);assert.equal(f.head(),receipt.publicCommit);assert.equal(receipt.privateTree,r.tree);assert.equal(f.git(f.fork,'rev-parse',`${receipt.publicCommit}^`),r.P);assert.equal(f.git(f.fork,'rev-parse',`${receipt.publicCommit}^{tree}`),r.tree);assert.notEqual(receipt.publicCommit,r.privateCommit);
    assert.ok(f.data.body.includes(`${f.pub.url}/commits/${receipt.publicCommit}`));assert.ok(f.data.body.includes(samples[0][1])||f.data.body.includes(samples[0][0]));assert.equal(parts(f.data.body).prefix,parts(baseBody).prefix);assert.equal(parts(f.data.body).suffix,parts(baseBody).suffix);
    const second=await x.cycle(),r2=await requestPublication(second.context);const latest=await f.advance('next-trunk','advanced\n');f.calls.failPatch=true;
    await assert.rejects(publish(f.pub,x.context.paths,r2,undefined,second.verify));const pushed=f.head();assert.notEqual(pushed,receipt.publicCommit);assert.notEqual(x.verified.at(-1),r2.P);f.git(f.fork,'merge-base','--is-ancestor',latest,pushed);
    f.calls.failPatch=false;f.data.body+='\nEdit made during recovery.';const n=x.verified.length;await reconcile(f.pub,x.context.paths,undefined,second.verify);assert.equal(f.head(),pushed);assert.equal(x.verified.length,n);assert.ok(f.data.body.endsWith('Edit made during recovery.'));assert.equal(parts(f.data.body).block.split('[PR #7]').length-1,2);
    const speed=await x.cycle(true),rs=await requestPublication(speed.context);await publish(f.pub,x.context.paths,rs,undefined,speed.verify);assert.equal(parts(f.data.body).block.split('[PR #7]').length-1,2);const h=f.head();
    const rejected=await x.cycle(),rr=await requestPublication(rejected.context);const writes=f.calls.writes;await f.advance('deny-fixture','new verdict\n');await assert.rejects(publish(f.pub,x.context.paths,rr,undefined,rejected.verify));assert.equal(f.head(),h);assert.equal(f.calls.writes,writes);
    console.log('Fixed PR: real leases and paired commits, two claims, interrupted push/PATCH repair, speed-only update and stale-evidence rejection verified offline');
  }finally{await x.close();}
}
