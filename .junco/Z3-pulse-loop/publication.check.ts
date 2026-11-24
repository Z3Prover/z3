import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdir, mkdtemp, rm, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { Publisher, emptyBlock, type Pull } from './publication.ts';
import { paths } from './state.ts';

/** Two real refs and an in-process PR. Only the API is simulated. */
export async function publicationFixture(reviewed = false) {
  const dir=await mkdtemp(join(process.env.PULSE_CHECK_TMPDIR ?? '/btrfs','pulse-pr-check-'));
  const repo=join(dir,'pr-7-publisher'), state=join(dir,'Z3-pulse-loop-pr-7'), trunk=join(dir,'official.git'), fork=join(dir,'fork.git'), author=join(dir,'author');
  const git=(cwd:string,...a:string[])=>execFileSync('/usr/bin/git',['-c','core.hooksPath=/dev/null','-c','user.name=Fixture','-c','user.email=fixture@example.invalid',...a],{cwd,env:{HOME:dir,PATH:'/usr/bin:/bin',GIT_CONFIG_NOSYSTEM:'1',GIT_CONFIG_GLOBAL:'/dev/null'},encoding:'utf8',stdio:['ignore','pipe','pipe']}).trimEnd();
  const commit=async(file:string,text:string)=>{await writeFile(join(author,file),text);git(author,'add','--',file);git(author,'commit','-qm',file);return git(author,'rev-parse','HEAD');};
  for(const r of [trunk,fork]) git(dir,'init','-q','--bare','--initial-branch=master',r);
  git(dir,'init','-q','--initial-branch=master',author);
  if (reviewed) {
    const objects=git(import.meta.dir,'rev-parse','--path-format=absolute','--git-path','objects');
    for (const db of [trunk,fork,join(author,'.git')]) await writeFile(join(db,'objects/info/alternates'),objects+'\n');
    git(author,'switch','--detach','803df8055301cf5e65a3a05a2402a5da678652dd'); git(author,'switch','-c','master');
  }
  await commit('base','base\n');git(author,'push',trunk,'HEAD:master');git(author,'switch','-qc','feat/junco-fstar');
  const first=await commit('feature','feature\n');git(author,'push',fork,'HEAD:feat/junco-fstar');git(author,'switch','-q','master');
  const advance=async(file:string,text:string)=>{const m=await commit(file,text);git(author,'push',trunk,'HEAD:master');return m;};
  const M=await advance('trunk','trunk\n');git(dir,'clone','-q','--no-local','-b','feat/junco-fstar',fork,repo);git(repo,'config','user.name','Fixture');git(repo,'config','user.email','fixture@example.invalid');
  const corpus=join(dir,'corpus');await mkdir(corpus);
  const p=paths({Z3_PULSE_LOOP_REPO:repo,Z3_PULSE_LOOP_STATE:state,Z3_PULSE_LOOP_CORPUS:corpus});
  const head=()=>git(fork,'rev-parse','refs/heads/feat/junco-fstar');
  const data={number:7,html_url:'https://github.com/Z3Prover/z3/pull/7',state:'open',merged:false,draft:false,user:{login:'elefthei'},base:{repo:{id:32944298,full_name:'Z3Prover/z3',default_branch:'master'},ref:'master'},head:{repo:{id:1426345895,full_name:'elefthei/z3'},ref:'feat/junco-fstar',sha:first},body:`Human introduction\n\n${emptyBlock}\n\nHuman footer.`} satisfies Pull;
  const calls={reads:0,writes:0,failPatch:false};const pub=await Publisher.fixture(7,p,trunk,fork,async(n,body)=>{assert.equal(n,7);if(body!==undefined){calls.writes++;if(calls.failPatch)throw Error('Fixture interrupted before PATCH');data.body=body;}else calls.reads++;return {...data,head:{...data.head,sha:head()}};});
  return {dir,p,repo,author,trunk,fork,git,pub,head,data,calls,advance,M,first,close:()=>rm(dir,{recursive:true,force:true})};
}
export async function checkPublisherParent() {
  const f=await publicationFixture();try {
    const binding=await f.pub.initialize(f.first);assert.equal(binding.upstream,f.M);assert.equal(binding.head,f.first);assert.notEqual(binding.seed,f.first);
    assert.equal(f.git(f.repo,'rev-parse',`${binding.seed}^`),f.M);assert.equal(f.git(f.repo,'show',`${binding.seed}:feature`),'feature');
    assert.equal((await f.pub.parent(f.first)).P,binding.seed);assert.equal(f.head(),f.first);
    f.data.state='closed';await assert.rejects(f.pub.parent(f.first),/PR authority/);f.data.state='open';
    f.data.number=8;await assert.rejects(f.pub.parent(f.first),/PR authority/);f.data.number=7;
    const moved=await f.advance('feature','conflicting official change\n');
    await assert.rejects(f.pub.parent(f.first));assert.equal(f.head(),f.first);assert.equal(f.calls.writes,0);
    assert.ok(f.git(f.repo,'diff','--name-only','--diff-filter=U').split('\n').includes('feature'));
    f.git(f.repo,'rebase','--abort');
    f.git(f.author,'push',f.fork,'HEAD:refs/heads/feat/junco-fstar','--force-with-lease=refs/heads/feat/junco-fstar:'+f.first);
    await assert.rejects(f.pub.parent(f.first),/outside publisher/);
    await assert.rejects(f.pub.push(binding.seed,f.first));assert.equal(f.head(),moved);assert.equal(f.calls.writes,0);
  } finally {await f.close();}
}
if(import.meta.main) await checkPublisherParent();
