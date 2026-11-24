// Literal YAML, scheduler and agent tools. Only the model and verifier measurements are offline fixtures.
import assert from 'node:assert/strict';
import { readFile, rename } from 'node:fs/promises';
import { join } from 'node:path';
import { contentText, fauxAssistantMessage, fauxProvider, fauxToolCall, InMemoryCredentialStore, type FauxResponseStep, type Message } from '@earendil-works/pi-ai';
import { ModelRuntime } from '@earendil-works/pi-coding-agent';
import { agent, graph, JuncoGraph, schedules, syntax, tools, tracer } from 'junco';
import type { TSchema } from 'typebox';
import { campaignParent, failureCode, makePublishTool, recordNode, regressionCycle, runCycle, scheduler, type Loop } from './wf.ts';
import { StateConflict } from './state.ts';
import { parts } from './publication.ts';
import { acceptedGraphFixture } from './publication.integration.check.ts';

const document = syntax.parse(await readFile(new URL('./wf.yml', import.meta.url), 'utf8'));
const cwd = process.argv[2];
assert.ok(cwd);
const id = graph.EdgeId.create;
const provider = 'pulse-wiring-fixture';
const faux = fauxProvider({api:provider, provider, models:[{id:'worker',reasoning:true},{id:'leader',reasoning:true,maxTokens:128}]});
const credentials = new InMemoryCredentialStore();
await credentials.modify(provider, async () => ({type:'api_key', key:'offline-fixture'}));
const models = await ModelRuntime.create({credentials,modelsPath:null,allowModelNetwork:false,refreshOnCreate:false});
models.registerNativeProvider(faux.provider);
const worker = {model:`${provider}/worker`,thinking:'high'} as const;
const leader = {model:`${provider}/leader`,thinking:'high'} as const;
const ladder = new schedules.ModelLadder(models,{smol:worker,low:worker,med:worker,high:leader,xhigh:leader});
const leaderId = graph.NodeId.create('Leader'), recordId = graph.NodeId.create('Record');
const assignment = 'Formula fixture-case.smt2. Diagnostic: prove fixture obligation #17.';
const plan = 'Plan: check lemma at fixture#17; falsify using a different key.';
const expectedTools = {Leader:['find','grep','publish_verified','read'],Developer:['bash','edit','find','grep','read','release']};
const call = (id:string) => fauxAssistantMessage([fauxToolCall('publish_verified',{}, {id})],{stopReason:'toolUse'});
function toolResult(messages: readonly Message[], id: string, error: boolean) {
  const result = messages.find(m => m.role === 'toolResult' && m.toolCallId === id);
  assert.ok(result?.role === 'toolResult');
  assert.equal(result.isError, error);
  return contentText(result.content);
}
process.umask(0o077);
const collection = await tools.ToolCollection.create(cwd,{bash:{commandPrefix:'ulimit -t 1800',spawnHook:() => { throw Error('No shell calls in the offline wiring check'); }}});
let closeFixture: (() => Promise<void>) | undefined;
try {
  const fixture = await acceptedGraphFixture();
  closeFixture = fixture.close;
  const {f} = fixture;
  const modes = ['idle','rejected','ci-red','local-accepted','stale-feedback','blank-writer','aborted-writer','wrong-tree','missing-receipt','blank-leader','nonterminal-leader','cancelled-leader','stale-evidence','measurement','accepted','blank-after-push'] as const;
  let localIteration = 0;
  for (const mode of modes) {
    const {context:seed,result:privateResult,verify} = mode === 'blank-after-push' ? await fixture.cycle() : fixture;
    const before = seed.selected!.before, item = seed.selected!.item!, verified = seed.verification!;
    const evidence = verified.report!.text;
    const originalHead = fixture.head(), originalBody = parts(fixture.body());
    const second = ['missing-receipt','blank-leader','nonterminal-leader','cancelled-leader','stale-evidence','measurement','accepted','blank-after-push'].includes(mode);
    const privateAccept = second || mode === 'wrong-tree' || mode === 'local-accepted';
    const active = mode !== 'idle' && mode !== 'stale-feedback';
    const iteration = privateAccept ? seed.iteration : ++localIteration;
    const x: Loop = {paths:seed.paths, sha:seed.sha, iteration, parent:seed.parent, attempt:seed.attempt, beforeOut:seed.beforeOut, publisher:mode === 'local-accepted' ? undefined : f.pub};
    const base = {sha:x.sha, out:seed.beforeOut!};
    const selected = {before, item:active ? item : null};
    const controller = new AbortController(), events: string[] = [];
    const task = graph.nodes.Task.create({kind:'prompt',text:assignment,spec:'One checked change with a falsifying case.'});
    const io = () => [f.calls.reads, f.calls.writes];
    const priorIO = io(), nBefore = faux.state.callCount;
    let planning: unknown;
    const api = makePublishTool(x, x.publisher ? verify : undefined);
    const code: Record<string, syntax.DeterministicNode<Loop>> = {
      Regress: regressionCycle(async (_c, _signal, received) => {
        assert.equal(received, iteration - 1);
        events.push('regress'); return base;
      }),
      Analytics: c=>{
        let published = false;
        return {state:new graph.nodes.Deterministic<TSchema,unknown>(async function*(){
          const inputs = yield [];
          assert.deepEqual(inputs.messages.get(id('Regress~>Analytics')),[base]);
          x.selected = selected; events.push('analytics');
          const send = (edge:string, value:unknown)=>graph.Message.create(c.edges.get(edge)!,value as TSchema);
          const outputs=[send('Analytics~>Record', selected)];
          if(active) outputs.push(send('Analytics~>Leader',task),send('Analytics~>Developer',task));
          else outputs.push(send('Analytics~>Verify',{idle:true}));
          published=true;
          yield outputs;
        },c.policy),is_available:(_view,triggered)=>triggered && !published};
      },
      Verify:c=>({state:new graph.nodes.Deterministic<TSchema,unknown>(async function*(){
        const inputs = yield [];
        if (!active){assert.deepEqual(inputs.messages.get(id('Analytics~>Verify')),[{idle:true}]);assert.equal(inputs.values.has(id('Developer->Verify')),false);}
        const report = active ? {text:syntax.finalText(inputs.values.get(id('Developer->Verify')),'Developer'),stopReason:'stop'} : null;
        if(report) assert.equal(report.text,evidence);
        const after = mode === 'ci-red' ? {...verified.after!,ciPass:false} : mode === 'wrong-tree' ? {...verified.after!,tree:'0'.repeat(40)} : privateAccept ? verified.after : null;
        const l = c.graph.result(leaderId);
        if (active) { assert.ok(l._tag === 'Some'); planning = l.value; }
        events.push('verify'); return x.verification = {after, changed: !!after, report};
      },c.policy)}),
      Record:recordNode(async (_p,input)=>{
        assert.equal(input.before,selected.before); assert.equal(input.item,selected.item); assert.equal(input.after,x.verification!.after);
        if (mode === 'ci-red') assert.match(input.reasons?.join() ?? '',/candidate build or corpus CI failed/);
        events.push('record');
        if (privateAccept) return privateResult; // Already archived by the real state.record() in this fixture.
        return {...privateResult,iteration:mode==='stale-feedback'?iteration-1:iteration,item:selected.item?.id ?? null,ok:false,commit:null,patch:null,after:null,report:input.report,reasons:input.reasons ?? ['idle'],accepted_change:0};
      }),
    };
    const execution=await JuncoGraph.fromYaml(document,{cwd,ladder,collection,code,context:x,signal:controller.signal,tools:{publish_verified:api},tracer:new tracer.DummyTracer(),scheduler});
    try {
      const originalLeader = execution.graph.getNode(leaderId)!.state;
      for(const [node,names] of Object.entries(expectedTools)){
        const state=execution.graph.getNode(graph.NodeId.create(node))?.state;
        assert.ok(state instanceof agent.JuncoAgent);
        assert.deepEqual(state.getActiveTools().map(t=>t.name).sort(),names);
      }
      if (mode === 'idle') {
        await execution.run();
        assert.deepEqual(events,[],'no cycle before source ingress');
        assert.equal(execution.graph.result(execution.graph.sink.id)._tag,'None');
      }
      const script: FauxResponseStep[] = [];
      if (active) {
        for (const role of ['leader','worker'] as const) {
          script.push((context,_options,_state,model)=>{
            const users = context.messages.flatMap(m=>m.role==='user'?[contentText(m.content)]:[]);
            assert.equal(model.id,role);
            assert.equal(users.length,2,'one staged instruction and one separately steered task');
            assert.ok(users[1]!.includes(task.taskId)); assert.equal(users[1]!.split(assignment).length-1,1);
            assert.ok(!users[0]!.includes(assignment));
            if(role==='worker') assert.ok(users[0]!.includes(plan));
            events.push(role);
            if(role==='leader' && mode==='accepted') return call('premature');
            if(role==='worker' && mode==='aborted-writer') controller.abort(new Error('fixture cancelled during Developer turn'));
            return fauxAssistantMessage(role==='leader'?plan:mode==='blank-writer'?'   ':evidence);
          });
          if (role==='leader' && mode==='accepted') script.push(ctx=>{
            assert.match(toolResult(ctx.messages,'premature',true), /No verified publication task/);
            assert.deepEqual(io(),priorIO);
            events.push('denied'); return fauxAssistantMessage(plan);
          });
        }
      }
      if (second) {
        script.push((ctx,_options,_state,model)=>{
          assert.equal(model.id,'leader'); assert.equal(execution.graph.getNode(leaderId)!.state,originalLeader);
          assert.ok(ctx.messages.some(m=>m.role==='assistant' && contentText(m.content)===plan),'same planning session');
          const tasks = ctx.messages.flatMap(m=>m.role==='user'?[contentText(m.content)]:[]);
          assert.ok(tasks.at(-1)?.includes(`verified iteration ${iteration} of PR #${f.pub.pr}`));
          const stillPlanning = execution.graph.result(leaderId);
          assert.ok(stillPlanning._tag==='Some' && stillPlanning.value === planning);
          assert.equal(execution.graph.available().has(recordId),false,'Record cannot consume the stale planning return');
          assert.deepEqual(io(),priorIO,'requesting a turn must not query the PR');
          events.push('publication');
          if (mode==='cancelled-leader') controller.abort(new Error('fixture cancelled during publication turn'));
          if (mode==='missing-receipt' || mode==='cancelled-leader') return fauxAssistantMessage('Published, according to the model.');
          if (mode==='blank-leader') return fauxAssistantMessage('  ');
          // Faux counts four characters per token. A short "length" response asks Pi to compact and retry.
          if (mode==='nonterminal-leader') return fauxAssistantMessage('part'.repeat(model.maxTokens),{stopReason:'length'});
          if (mode==='stale-evidence') x.verification = {...x.verification!,after:{...verified.after!,tree:'0'.repeat(40)}};
          if (mode==='measurement') process.env.JUNCO_GRAPH_RUN_DIR = cwd;
          return call('publish');
        });
        if (mode==='stale-evidence' || mode==='measurement') script.push(ctx=>{
          assert.match(toolResult(ctx.messages,'publish',true), /No verified publication task|Stale publication permission/);
          assert.deepEqual(io(),priorIO); events.push('denied'); return fauxAssistantMessage('No receipt.');
        });
        if (mode==='blank-after-push') script.push(ctx=>{
          assert.equal(toolResult(ctx.messages,'publish',false), `${f.pub.url}/commits/${fixture.head()}`);
          events.push('published'); return fauxAssistantMessage('  ');
        });
        if (mode==='accepted') {
          let updated: number[];
          script.push(ctx=>{
            assert.equal(toolResult(ctx.messages,'publish',false), `${f.pub.url}/commits/${fixture.head()}`);
            updated = io(); events.push('published'); return call('duplicate');
          },ctx=>{
            const text = toolResult(ctx.messages,'duplicate',false);
            assert.equal(text,`${f.pub.url}/commits/${fixture.head()}`); assert.deepEqual(io(),updated);
            events.push('duplicate'); return fauxAssistantMessage(text);
          });
        }
      }
      faux.setResponses(script);
      const cycle = runCycle(execution,x,iteration-1,controller.signal);
      if (second && mode!=='accepted' || mode==='wrong-tree') {
        await assert.rejects(cycle,(err:unknown)=>err instanceof StateConflict && failureCode([err],true,controller.signal.aborted,false,false)===78);
        assert.equal(execution.graph.result(execution.graph.sink.id)._tag,'None');
        if (mode==='blank-after-push') {
          assert.notEqual(fixture.head(),originalHead); assert.equal(f.calls.writes,priorIO[1]!+1);
          await assert.rejects(campaignParent(x.paths,f.pub,controller.signal),/lacks a confirmed final Leader return/);
          assert.equal(fixture.verified.length,2); assert.equal(f.calls.writes,priorIO[1]!+1);
        } else {
          assert.equal(fixture.head(),originalHead); assert.deepEqual(io(),priorIO);
          if (second) {
            const dir=join(x.paths.state,'runs',String(iteration),'publication');
            const saved=JSON.parse(await readFile(join(dir,'request.json'),'utf8'));
            assert.equal(saved.privateCommit,privateResult.commit); assert.equal(saved.tree,seed.attempt!.tree);
            // Preserve this parked trial and start the next graph at the same immutable private decision.
            await rename(dir,join(f.dir,`parked-${mode}`));
          }
        }
      } else if(mode==='blank-writer'||mode==='aborted-writer'||mode==='stale-feedback') {
        await assert.rejects(cycle);
        assert.equal(execution.graph.result(execution.graph.sink.id)._tag,'None');
      } else {
        const {result}=await cycle; assert.equal(result,x.result);
        for (const n of [recordId,graph.NodeId.create('Regress'),execution.graph.sink.id]) {
          const ret=execution.graph.result(n); assert.ok(ret._tag==='Some' && ret.value===result);
        }
        if(mode==='accepted'){
          const h=fixture.head(),body=parts(fixture.body());
          assert.notEqual(h,originalHead); assert.notEqual(h,result.commit);
          assert.equal(f.git(f.fork,'rev-parse',`${h}^`),seed.parent!.P); assert.equal(f.git(f.fork,'rev-parse',`${h}^{tree}`),seed.attempt!.tree);
          assert.equal(body.prefix,originalBody.prefix); assert.equal(body.suffix,originalBody.suffix);
          assert.equal(body.block.split('[PR #7]').length-1,1); assert.ok(body.block.includes(`${f.pub.url}/commits/${h}`));
          assert.equal(f.calls.writes,priorIO[1]!+1); assert.equal(fixture.verified.length,1);
        } else { assert.deepEqual(io(),priorIO); assert.equal(fixture.head(),originalHead); }
        events.push('sink');
      }
      const expected=['regress','analytics',...(active?['leader',...(mode==='accepted'?['denied']:[]),'worker']:[])];
      if(mode!=='aborted-writer' && mode!=='blank-writer') expected.push('verify','record');
      if(second) expected.push('publication');
      if(mode==='accepted') expected.push('published','duplicate');
      if(mode==='blank-after-push') expected.push('published');
      if(mode==='stale-evidence'||mode==='measurement') expected.push('denied');
      if(['idle','local-accepted','rejected','ci-red','accepted'].includes(mode)) expected.push('sink');
      assert.deepEqual(events,expected);
      assert.equal(faux.state.callCount-nBefore,script.length);
      console.log(`${mode}: ${events.join(' -> ')}`);
    }finally{delete process.env.JUNCO_GRAPH_RUN_DIR; await execution.graph.close();}
  }
}finally{try{await closeFixture?.();}finally{await collection.close();}}
