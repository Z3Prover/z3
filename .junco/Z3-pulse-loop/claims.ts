import { createHash, randomUUID } from 'node:crypto';
import { createReadStream } from 'node:fs';
import { link, lstat, mkdtemp, readFile, realpath, rm, writeFile } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import { CORPORA, evaluationPaths, must, prCandidateFailure, validateScope, type Analysis } from './evaluation.ts';
import { check, digest, oid } from './publication.ts';
import type { Paths } from './state.ts';

export type Pair = { p:Paths; parent:string; tree:string; beforeOut:string; afterOut:string; before:Analysis; after:Analysis };
export type Claim = { kind:'lemma'|'formula'; key:string; name:string; path:string; line?:number; type?:string; sha256?:string };
const corpusPin = '91c60596fd6a43de189a1ccba8080a3b48797537';
const fstarPin = '360741f618a1882b3bb6273afc98e7d564b76448c7a96b00d60c71c0d3abb46a';
const manifest = 'fstar/tools/checker_modules.json';
const git = (cwd:string, signal:AbortSignal|undefined, ...args:string[]) => must(['/usr/bin/git','--no-optional-locks','-c','core.fsmonitor=false',...args], {cwd,signal});
async function regular(path:string) {
  check((await lstat(path)).isFile() && await realpath(path) === resolve(path), `Nonregular claim input: ${path}`);
  return path;
}
async function fileDigest(path:string) {
  const h=createHash('sha256'); for await(const b of createReadStream(await regular(path))) h.update(b); return h.digest('hex');
}

type CorpusInput = {paths:string[]; sha256:Record<string,string>};
type Evidence = { out:string; a:Analysis; ep:Paths; rev:string; hashes:Record<string,string>; artifact:(name:string)=>Promise<string>; id:{corpora:CorpusInput[]}; files:string[] };

// analyze() authenticated this inventory against the build, the pinned corpus and the exact toolchain.
async function evidence(p:Paths, out:string, a:Analysis, signal?:AbortSignal):Promise<Evidence> {
  const data=await readFile(await regular(join(out,'evidence.json')));
  check(digest(data)===a.evidenceSha256,'Stale claim evidence inventory');
  const hashes:Record<string,string>=JSON.parse(data.toString());
  const artifact=async (name:string) => {
    const bytes=await readFile(await regular(join(out,name)));
    check(digest(bytes)===hashes[name],`Changed claim evidence: ${name}`); return bytes.toString();
  };
  const [build,id,scope]=await Promise.all(['build.json','evaluator.json','scope-ocaml.json'].map(async f=>JSON.parse(await artifact(f))));
  const ep=evaluationPaths(p,out), rev=oid(build.source_sha);
  check(build.exit_code===0 && build.sha===a.sha && build.tree===a.tree && build.evaluator===a.evaluator &&
    digest(JSON.stringify(id))===a.evaluator && id.policy==='upstream-pr-v1' && id.parent===a.sha &&
    id.upstream===p.reviewedUpstream && id.corpusCommit===corpusPin && id.fstarSha256===fstarPin,'Wrong claim evaluation identity');
  const heads=(await git(ep.worktree,signal,'rev-parse','HEAD','HEAD^{tree}')).trim().split('\n');
  check(heads[0]===rev && heads[1]===a.tree,'Wrong source for checked declarations');
  const registered=JSON.parse(await git(ep.worktree,signal,'cat-file','blob',`${rev}:${manifest}`));
  validateScope(scope,registered.modules,registered.tests,rev,id.fstar);
  return {out,a,ep,rev,hashes,artifact,id,files:scope.selected_modules as string[]};
}

async function formulaClaims(before:Evidence, after:Evidence, prior:Claim[], signal?:AbortSignal) {
  const result:Claim[]=[], previous=new Set(prior.filter(c=>c.kind==='formula').map(c=>c.path));
  for(const [n,suite] of CORPORA.entries()) {
    const input=after.id.corpora[n];
    const paths=input.paths.filter(path=>after.a.cases[path]?.outcome==='ACCEPT' && (previous.has(path)||before.a.cases[path]?.outcome!=='ACCEPT'));
    if(!paths.length) continue;
    const readSuite=async (s:Evidence) => {
      const selected=JSON.parse(await s.artifact(`${suite.name}/selection.json`));
      const rows=(await s.artifact(`${suite.name}/results.jsonl`)).trimEnd().split('\n').map(l=>JSON.parse(l));
      check(selected.corpus_commit===corpusPin && selected.z3_commit===s.rev && selected.corpus_path===suite.path &&
        JSON.stringify(selected.paths)===JSON.stringify(input.paths) && rows.length===input.paths.length,'Wrong pinned formula selection');
      return async (path:string,i:number) => {
        const r=rows[i], stdout=`logs/${String(i).padStart(6,'0')}.stdout`;
        check(r.path===path && r.stdout===stdout && r.outcome===s.a.cases[path]?.outcome &&
          (!suite.manifest || (r.input_sha256===input.sha256[path] && selected.input_sha256?.[path]===input.sha256[path])),`Wrong formula evidence for ${path}`);
        const text=(await s.artifact(`${suite.name}/${stdout}`)).trim();
        const accepted=r.returncode===0 && text==='ACCEPT';
        check(r.verdict===text && (r.outcome==='ACCEPT')===accepted && (Number.isInteger(r.returncode)||r.returncode===null),`Incorrect native verdict/exit: ${path}`);
        return accepted;
      };
    };
    const [old,updated]=await Promise.all([readSuite(before),readSuite(after)]);
    for(const path of paths) {
      signal?.throwIfAborted();
      check(path.startsWith(suite.path+'/') && path.endsWith('.smt2') && path.split('/').every(x=>x && x!=='.' && x!=='..'), 'Invalid pinned SMT-LIB path');
      const i=input.paths.indexOf(path), sha256=await fileDigest(join(after.ep.corpus,path));
      check(sha256===input.sha256[path],'Pinned formula input hash changed');
      const [was,now]=await Promise.all([old(path,i),updated(path,i)]);
      check(now && (!was||previous.has(path)),`Formula did not become certified: ${path}`);
      result.push({kind:'formula',key:`${corpusPin}:${path}:${sha256}`,name:path,path,sha256});
    }
  }
  return result;
}

type Lemma={claim:Claim; declaration:string};
function readDeclarations(text:string, tag:string, name:string, source:string) {
  const start=`TAC>> ${tag}\n`, end=`\n${tag} END\n`, done=`TAC>> ${tag} DONE\n`;
  check(text.split(done).length===2,'Incomplete compiler inspection');
  const lines=source.split('\n'), found:Lemma[]=[];
  for(const entry of text.slice(0,text.indexOf(done)).split(start).slice(1)) {
    const stop=entry.indexOf(end); check(stop>=0,'Truncated checked declaration');
    const [q,file,range,...signature]=entry.slice(0,stop).split('\n'), type=signature.join('\n');
    check(q.startsWith(name+'.') && !/[\x00-\x1f\x7f]/.test(q) && file===`${name}.fst` && type.trim() && /^\d+:\d+:\d+:\d+$/.test(range),'Invalid checked theorem metadata');
    const [l,c,to,d]=range.split(':').map(Number);
    check(l>=1 && l<=to && to<=lines.length && (l<to || c<d),'Invalid F* declaration range');
    // F* source columns are Unicode scalar offsets, not UTF-16 or UTF-8 offsets.
    const first=Array.from(lines[l-1]), last=l===to ? first : Array.from(lines[to-1]);
    check(c<=first.length && d<=last.length,'Declaration range exceeds checked source');
    const declaration=l===to ? first.slice(c,d).join('') : [first.slice(c).join(''),...lines.slice(l,to-1),last.slice(0,d).join('')].join('\n');
    found.push({claim:{kind:'lemma',key:`${q}:${digest(type)}`,name:q,path:`fstar/${file}`,line:l,type},declaration});
  }
  return found;
}

async function lemmas(s:Evidence, wanted:Set<string>, signal?:AbortSignal) {
  const files=s.files.filter(f=>wanted.has(`fstar/${f}`) && f.endsWith('.fst')), found=new Map<string,Lemma>();
  if(!files.length) return found;
  check(await fileDigest(s.ep.fstarExe)===fstarPin,'Wrong F* executable for checked theorem inspection');
  const tmp=await mkdtemp(join(s.out,'inspect-'));
  try {
    // Only the checked, selected closure enters the compiler search path. No plugins or inputs from the developer's checkout.
    for(const file of s.files) {
      signal?.throwIfAborted();
      check(/^Z3[A-Za-z0-9_]+\.fsti?$/.test(file),'Unexpected verified module name');
      const cache=`${file}.checked`, input=join(s.ep.fstarCache,cache);
      check(await fileDigest(input)===s.hashes[`fstar-cache/${cache}`],`Stale checked module: ${file}`);
      await link(input,join(tmp,cache));
      const source=await git(s.ep.worktree,signal,'cat-file','blob',`${s.rev}:fstar/${file}`);
      await writeFile(join(tmp,file),source,{flag:'wx',mode:0o400});
    }
    const tool='PulseClaimInspection', tags=files.map(()=>randomUUID()), script=await readFile(join(import.meta.dir,`${tool}.fst`),'utf8');
    const actions=files.map((f,i)=>`%splice[] (report (top_env ()) "${f.slice(0,-4)}" "${tags[i]}"; [])`);
    await writeFile(join(tmp,`${tool}.fst`),[script,...actions,''].join('\n'),{flag:'wx',mode:0o400});
    // --expose_interfaces is for this metadata query only; the ordinary strict build discharged the proofs.
    const output=await must([s.ep.fstarExe,'--warn_error','@1..999','--cache_dir','.', '--already_cached',`* -${tool}`,
      '--ext','fly_deps=0','--expose_interfaces','--print_implicits','--print_universes',...files,`${tool}.fst`],{cwd:tmp,signal,timeoutMs:180_000});
    for(const [i,f] of files.entries()) for(const lemma of readDeclarations(output,tags[i],f.slice(0,-4),await readFile(join(tmp,f),'utf8'))) {
      const old=found.get(lemma.claim.name);
      // defs_in_module can return the same let group once per mutually recursive binding.
      check(!old || (old.claim.key===lemma.claim.key && old.declaration===lemma.declaration && old.claim.line===lemma.claim.line),'Ambiguous checked declaration');
      found.set(lemma.claim.name,lemma);
    }
    return found;
  } finally { await rm(tmp,{recursive:true,force:true}); }
}

export async function extractClaims(pair:Pair, prior:Claim[], signal?:AbortSignal):Promise<Claim[]> {
  const {p,parent,tree,before:b,after:a}=pair;
  check(p.reviewedUpstream && b.sha===oid(parent) && a.sha===parent && a.tree===oid(tree) && b.evaluator===a.evaluator && b.buildOk && prCandidateFailure(a)===null,'Claims require a complete verified pair');
  const [before,after]=await Promise.all([evidence(p,pair.beforeOut,b,signal),evidence(p,pair.afterOut,a,signal)]);
  check(before.rev===parent && (await git(after.ep.worktree,signal,'rev-parse',`${after.rev}^`)).trim()===parent,'Wrong checked parent for claim comparison');
  const changed=new Set((await git(after.ep.worktree,signal,'diff-tree','-r','--no-renames','--name-only','-z',parent,tree,'--','fstar/*.fst')).split('\0').filter(Boolean));
  const wanted=new Set([...changed,...prior.filter(c=>c.kind==='lemma').map(c=>c.path)]), previous=new Set(prior.map(c=>c.key));
  const old=await lemmas(before,changed,signal), current=await lemmas(after,wanted,signal), rows=await formulaClaims(before,after,prior,signal);
  for(const {claim,declaration} of current.values()) {
    const existed=old.get(claim.name);
    if(previous.has(claim.key) || (changed.has(claim.path) && (existed?.claim.key!==claim.key || existed.declaration!==declaration))) rows.push(claim);
  }
  const byKey=new Map(rows.map(c=>[c.key,c]));
  for(const prev of prior) {
    const c=byKey.get(prev.key);
    check(c && prev.kind===c.kind && prev.name===c.name && prev.path===c.path && prev.type===c.type && prev.sha256===c.sha256,`Previously published claim no longer substantiated: ${prev.key}`);
  }
  return [...byKey.values()].sort((x,y)=>x.kind<y.kind?-1:x.kind>y.kind?1:x.key<y.key?-1:x.key>y.key?1:0);
}
