import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdir, mkdtemp, readFile, readdir, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { extractClaims, type Pair } from './claims.ts';
import { CORPORA, must, sh, type Analysis } from './evaluation.ts';
import { digest } from './publication.ts';
import { paths } from './state.ts';

const pin='91c60596fd6a43de189a1ccba8080a3b48797537', compiler='360741f618a1882b3bb6273afc98e7d564b76448c7a96b00d60c71c0d3abb46a';
const moduleFile='Z3ClaimFixture.fst', iface='Z3ClaimSignature.fsti', selected=[iface,moduleFile];
const unchanged=`module Z3ClaimFixture
module Signature = Z3ClaimSignature
let ident (x:int) : int = x
assume val only_assumed : x:int -> Lemma (x == x)
let existing (x:int) : Lemma (requires (x > 0)) (ensures (x >= 1)) = ()
`;
const addition='let plus_zero (x:int) : Lemma (x + 0 == x) = ()\n';
const git=(cwd:string,...args:string[])=>execFileSync('/usr/bin/git',['-c','core.hooksPath=/dev/null','-c','commit.gpgsign=false',...args],{cwd,encoding:'utf8',stdio:['ignore','pipe','pipe'],env:{PATH:'/usr/bin:/bin',HOME:'/nonexistent',GIT_CONFIG_GLOBAL:'/dev/null',GIT_CONFIG_NOSYSTEM:'1',GIT_ALLOW_PROTOCOL:'file',GIT_AUTHOR_NAME:'fixture',GIT_AUTHOR_EMAIL:'fixture@localhost',GIT_COMMITTER_NAME:'fixture',GIT_COMMITTER_EMAIL:'fixture@localhost'}}).trimEnd();
const save=async(path:string,bytes:string)=>{await mkdir(dirname(path),{recursive:true}); await writeFile(path,bytes);};

export async function checkClaims() {
  const root=await mkdtemp(join(process.env.PULSE_CHECK_TMPDIR??tmpdir(),'pulse-claims-'));
  try {
    const beforeOut=join(root,'before'), base=join(beforeOut,'source'), corpus=join(root,'corpus'), version=process.env.FSTAR_EXE;
    await mkdir(base,{recursive:true}); git(base,'init','--template=','--quiet');
    await save(join(base,'fstar/tools/checker_modules.json'),JSON.stringify({modules:selected,tests:[],cherry_modules:[]}));
    await save(join(base,'fstar',iface),'module Z3ClaimSignature\nval declaration_only : x:int -> Lemma (x == x)\n');
    await save(join(base,'fstar',moduleFile),unchanged); git(base,'add','fstar'); git(base,'commit','-qm','baseline');
    const parent=git(base,'rev-parse','HEAD'), p={...paths(),state:root,worktree:base,repo:base,reviewedUpstream:parent,corpus};
    const fork=async (name:string, proof?:string)=>{
      const out=join(root,name), source=join(out,'source'); await mkdir(out); git(out,'clone','-q','--no-local',base,source);
      if(proof) {
        // Move the existing declaration too: a line-number change alone is not a new theorem.
        await save(join(source,'fstar',moduleFile),unchanged.replace('let existing','\nlet existing')+proof);
        await save(join(source,'fstar/Z3Unselected.fst'),'module Z3Unselected\n'+addition);
      } else await save(join(source,'performance.txt'),'timing-only fixture');
      git(source,'add','.'); git(source,'commit','-qm',name); return out;
    };
    const spec='(set-logic QF_LIA)\n(assert false)\n(check-sat)\n', hash=digest(spec);
    const corpora=CORPORA.map(c=>{const paths=Array.from({length:c.size},(_,i)=>`${c.path}/case${i}.smt2`); return {paths,sha256:Object.fromEntries(paths.map(x=>[x,hash]))};});
    const path=corpora[1].paths[0]; await save(join(corpus,path),spec);
    const identity={policy:'upstream-pr-v1',upstream:parent,parent,corpusCommit:pin,fstarSha256:compiler,fstar:version ? await must([version,'--version'],{cwd:root}) : 'offline native-evidence fixture',corpora};
    const evaluator=digest(JSON.stringify(identity));
    const strict=async(out:string)=>{
      assert.ok(version); const dir=join(out,'source/fstar'), cache=join(out,'fstar-cache'); await mkdir(cache);
      for(const file of selected) await must([version,'--warn_error','@1..999','--cache_checked_modules','--cache_dir',cache,'--include',cache,file],{cwd:dir});
    };
    // These are native protocol controls, not a substitute for a scored campaign build.
    async function evidence(out:string,outcome:string,code:number,stdout:string,recordedHash=hash):Promise<Analysis> {
      const source=join(out,'source'), rev=git(source,'rev-parse','HEAD'), tree=git(source,'rev-parse','HEAD^{tree}');
      const table:Record<string,string>={};
      const put=async(name:string,s:string)=>{await save(join(out,name),s);table[name]=digest(s);};
      await put('build.json',JSON.stringify({exit_code:0,sha:parent,tree,evaluator,source_sha:rev})); await put('evaluator.json',JSON.stringify(identity));
      await put('scope-ocaml.json',JSON.stringify({source_sha:rev,backend:'ocaml',mode:'full',native_tests:true,fstar:identity.fstar.trim(),selected_count:selected.length,selected_modules:selected,registered_not_selected:[]}));
      if(version) for(const file of (await readdir(join(out,'fstar-cache'))).sort()) if(file.endsWith('.checked')) table[`fstar-cache/${file}`]=digest(await readFile(join(out,'fstar-cache',file)));
      const cases:Analysis['cases']={};
      for(const [n,c] of CORPORA.entries()) {
        const inputs=corpora[n]; await put(`${c.name}/selection.json`,JSON.stringify({corpus_path:c.path,corpus_commit:pin,z3_commit:rev,paths:inputs.paths,input_sha256:inputs.sha256}));
        const rows=inputs.paths.map((x,i)=>{
          const target=x===path, stem=`logs/${String(i).padStart(6,'0')}`; cases[x]={outcome:target?outcome:'SAT',wall:0};
          return {path:x,returncode:target?code:4,outcome:cases[x].outcome,verdict:target?stdout.trim():'SAT',stdout:`${stem}.stdout`,stderr:`${stem}.stderr`,input_sha256:target?recordedHash:hash};
        });
        await put(`${c.name}/results.jsonl`,rows.map(r=>JSON.stringify(r)).join('\n')+'\n');
        if(n===1) await put(`${c.name}/logs/000000.stdout`,stdout);
      }
      const data=JSON.stringify(table); await save(join(out,'evidence.json'),data);
      const counts:Record<string,number>={}; for(const c of Object.values(cases)) counts[c.outcome]=(counts[c.outcome]??0)+1;
      return {sha:parent,tree,evaluator,evidenceSha256:digest(data),buildOk:true,ciPass:true,tested:242,counts,cases,statsCases:0,pending:0,proofNodes:0,checkMs:0,solveMs:0,families:[],lemmas:0,assumed:0};
    }
    const out=await fork('performance'); if(version) {await strict(beforeOut); await strict(out);}
    const before=await evidence(beforeOut,'PARTIAL',3,'PARTIAL 1\n');
    const pair=(afterOut:string,after:Analysis):Pair=>({p,parent,tree:after.tree,beforeOut,afterOut,before,after});
    const native=async(o:string,c:number,s:string,h?:string)=>pair(out,await evidence(out,o,c,s,h));
    const initial=await native('ACCEPT',0,'ACCEPT\n'), rows=await extractClaims(initial,[]);
    assert.deepEqual(rows,[{kind:'formula',key:`${pin}:${path}:${hash}`,name:path,path,sha256:hash}]);
    assert.deepEqual(await extractClaims(initial,[...rows,...rows]),rows);
    const already={...initial,before:await evidence(beforeOut,'ACCEPT',0,'ACCEPT\n')};
    assert.deepEqual(await extractClaims(already,[]),[]);
    assert.deepEqual(await extractClaims(already,rows),rows);
    assert.equal((await evidence(beforeOut,'PARTIAL',3,'PARTIAL 1\n')).evidenceSha256,before.evidenceSha256);
    assert.deepEqual(await extractClaims(await native('PARTIAL',3,'PARTIAL 1\n'),[]),[]);
    await assert.rejects(extractClaims(await native('PARTIAL',3,'PARTIAL 1\n'),rows),/no longer substantiated/);
    await assert.rejects(extractClaims(await native('ACCEPT',1,'ACCEPT\n'),[]),/native verdict/);
    await assert.rejects(extractClaims(await native('ACCEPT',0,'ACCEPT\nSAT\n'),[]),/native verdict/);
    await assert.rejects(extractClaims(await native('ACCEPT',0,'ACCEPT\n','f'.repeat(64)),[]),/Wrong formula evidence/);
    const restored=await native('ACCEPT',0,'ACCEPT\n'); await writeFile(join(corpus,path),spec+'; changed');
    await assert.rejects(extractClaims(restored,[]),/input hash changed/); await writeFile(join(corpus,path),spec);
    await writeFile(join(out,'smtlib-sample/logs/000000.stdout'),'REJECT\n'); await assert.rejects(extractClaims(restored,[]),/Changed claim evidence/);
    if(version) {
      const proof=await fork('proof',addition); await strict(proof);
      const approved=pair(proof,await evidence(proof,'PARTIAL',3,'PARTIAL 1\n'));
      const checked=await extractClaims(approved,[]);
      assert.deepEqual(checked.map(c=>[c.kind,c.name,c.path,c.line]),[['lemma','Z3ClaimFixture.plus_zero',`fstar/${moduleFile}`,7]]);
      assert.match(checked[0].type!,/ensures/); assert.equal(checked[0].key,`${checked[0].name}:${digest(checked[0].type!)}`);
      const weaker=await fork('changed-statement',addition.replace('Lemma (x + 0 == x)','Lemma (requires (x > 0)) (ensures (x + 0 == x))')); await strict(weaker);
      const revised=pair(weaker,await evidence(weaker,'PARTIAL',3,'PARTIAL 1\n'));
      const [conditional]=await extractClaims(revised,[]); assert.match(conditional.type!,/requires[\s\S]*ensures/);
      assert.notEqual(conditional.key,checked[0].key);
      await assert.rejects(extractClaims(revised,checked),/no longer substantiated/);
      await assert.rejects(extractClaims(await native('PARTIAL',3,'PARTIAL 1\n'),checked),/no longer substantiated/);
      await save(join(root,'Z3BadProof.fst'),'module Z3BadProof\nlet false_proof (x:int) : Lemma (x > x) = ()\n');
      const failed=await sh([version,'--warn_error','@1..999','Z3BadProof.fst'],{cwd:root});
      assert.notEqual(failed.code,0); assert.match(failed.stderr+failed.stdout,/Failed to prove: x > x/);
    }
  } finally { await rm(root,{recursive:true,force:true}); }
}
