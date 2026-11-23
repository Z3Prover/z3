// Offline topology check: actual scheduler and role tools, in-memory Pi responses, no corpus or patch.
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { contentText, fauxAssistantMessage, fauxProvider, InMemoryCredentialStore } from '@earendil-works/pi-ai';
import { ModelRuntime } from '@earendil-works/pi-coding-agent';
import { agent, graph, JuncoGraph, schedules, syntax, tools, tracer } from 'junco';
import type { TSchema } from 'typebox';
import { scheduler } from './wf.ts';

const document = syntax.parse(await readFile(new URL('./wf.yml', import.meta.url), 'utf8'));
const cwd = process.argv[2];
assert.ok(cwd);
const id = graph.EdgeId.create;
const provider = 'pulse-wiring-fixture';
const faux = fauxProvider({api:provider, provider, models:[{id:'worker',reasoning:true},{id:'leader',reasoning:true}]});
const credentials = new InMemoryCredentialStore();
await credentials.modify(provider, async () => ({type:'api_key', key:'offline-fixture'}));
const models = await ModelRuntime.create({credentials,modelsPath:null,allowModelNetwork:false,refreshOnCreate:false});
models.registerNativeProvider(faux.provider);
const worker = {model:`${provider}/worker`,thinking:'high'} as const;
const leader = {model:`${provider}/leader`,thinking:'high'} as const;
const ladder = new schedules.ModelLadder(models,{smol:worker,low:worker,med:worker,high:leader,xhigh:leader});
const baseline = {sha:'fixture-tip',out:'fixture-reports'};
const before = {tested:1,accept:0};
const item = {id:'fixture:item'};
const assignment = 'Formula fixture-case.smt2. Diagnostic: prove fixture obligation #17.';
const plan = 'Plan: check lemma at fixture#17; falsify using a different key.';
const evidence = 'Title: fixture evidence\nCase retained its pending obligation.';
const expectedTools = {leader:['find','grep','read'],worker:['bash','edit','find','grep','read','release']};
const collection = await tools.ToolCollection.create(cwd,{bash:{commandPrefix:'ulimit -t 1800',spawnHook:() => { throw Error('No shell calls in the offline wiring check'); }}});
try {
  for (const mode of ['idle','assigned','blank-writer','aborted-writer'] as const) {
    const active = mode !== 'idle';
    const controller = new AbortController();
    const calls: string[] = [];
    let recordCalls = 0;
    const task = graph.nodes.Task.create({kind:'prompt',text:assignment,spec:'One checked change with a falsifying case.'});
    const nBefore = faux.state.callCount;
    faux.setResponses(active ? (['leader','worker'] as const).map(role => (context, _options, _state, model) => {
      const users = context.messages.flatMap(m=>m.role==='user' ? [contentText(m.content)] : []);
      assert.equal(model.id,role);
      assert.equal(users.length,2,'one staged instruction and one separately steered task');
      assert.ok(users[1]!.includes(task.taskId));
      assert.equal(users[1]!.split(assignment).length-1,1);
      assert.ok(!users[0]!.includes(assignment));
      if (role === 'worker') assert.ok(users[0]!.includes(plan));
      calls.push(role);
      if(role==='worker' && mode==='aborted-writer') controller.abort(new Error('fixture cancelled during writer request'));
      return fauxAssistantMessage(role==='leader' ? plan : mode==='blank-writer' ? '   ' : evidence);
    }) : []);
    const code: Record<string, syntax.DeterministicNode> = {
      Regress: c=>({state:new graph.nodes.Deterministic<TSchema,unknown>(async function*(){return baseline;},c.policy)}),
      Analytics: c=>{
        let published = false;
        return {state:new graph.nodes.Deterministic<TSchema,unknown>(async function*(){
          const inputs = yield [];
          assert.deepEqual(inputs.values.get(id('Regress->Analytics')),baseline);
          const send = (edge:string, value:unknown)=>graph.Message.create(c.edges.get(edge)!,value as TSchema);
          const outputs=[send('Analytics~>Record',{before,item:active?item:null})];
          if(active) outputs.push(send('Analytics~>Leader',task),send('Analytics~>Developer',task));
          else outputs.push(send('Analytics~>Verify',{idle:true}));
          published=true;
          yield outputs;
        },c.policy),is_available:(_view,triggered)=>triggered && !published};
      },
      Verify:c=>({state:new graph.nodes.Deterministic<TSchema,unknown>(async function*(){
        const inputs = yield [];
        if (!active){assert.deepEqual(inputs.messages.get(id('Analytics~>Verify')),[{idle:true}]);assert.equal(inputs.values.has(id('Developer->Verify')),false);}
        const report = active ? {text:syntax.finalText(inputs.values.get(id('Developer->Verify')),'Developer')} : null;
        if(report) assert.equal(report.text,evidence);
        return {after:null,changed:false,report};
      },c.policy)}),
      Record:c=>({state:new graph.nodes.Deterministic<TSchema,unknown>(async function*(){
        const inputs=yield [];
        assert.deepEqual(inputs.messages.get(id('Analytics~>Record')),[{before,item:active?item:null}]);
        const verified=inputs.values.get(id('Verify->Record')) as {after:null;changed:boolean;report:{text:string}|null};
        assert.equal(verified.report?.text ?? null,active?evidence:null);
        recordCalls++;
        return {iteration:1,item:active?item.id:null,base:baseline.sha,ok:false,reasons:[active?'no patch':'idle'],before,after:null,report:verified.report,title:active?'fixture evidence':null,patch:null,commit:null};
      },c.policy)}),
    };
    const execution=await JuncoGraph.fromYaml(document,{cwd,ladder,collection,code,signal:controller.signal,tracer:new tracer.DummyTracer(),scheduler});
    try {
      for(const [node,names] of [['Leader',expectedTools.leader],['Developer',expectedTools.worker]] as const){
        const state=execution.graph.getNode(graph.NodeId.create(node))?.state;
        assert.ok(state instanceof agent.JuncoAgent);
        assert.deepEqual(state.getActiveTools().map(t=>t.name).sort(),names);
      }
      if(mode==='blank-writer'||mode==='aborted-writer'){
        await assert.rejects(async()=>{
          await execution.run({signal:controller.signal});
          controller.signal.throwIfAborted();
        });
        assert.equal(execution.graph.result(execution.graph.sink.id)._tag,'None');
        assert.equal(recordCalls,0);
      }else{
        await execution.run();
        const result=execution.graph.result(execution.graph.sink.id);
        assert.equal(result._tag,'Some');
        if(result._tag==='Some')assert.deepEqual(result.value,{iteration:1,item:active?item.id:null,base:baseline.sha,ok:false,reasons:[active?'no patch':'idle'],before,after:null,report:active?{text:evidence}:null,title:active?'fixture evidence':null,patch:null,commit:null});
        assert.equal(recordCalls,1);
      }
      assert.deepEqual(calls,active?['leader','worker']:[]);
      assert.equal(faux.state.callCount-nBefore,active?2:0);
      console.log(`${mode}: ${JSON.stringify(calls)}, Record activations ${recordCalls}, sink ${execution.graph.result(execution.graph.sink.id)._tag}`);
    }finally{await execution.graph.close();}
  }
}finally{await collection.close();}
