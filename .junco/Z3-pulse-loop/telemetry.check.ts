import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { join } from 'node:path';
import { JuncoGraph, graph, schedules, tracer } from 'junco';
import { JuncoFrontend } from 'junco-frontend';
import { pairedRecorder } from './telemetry.ts';
import type { TSchema } from 'typebox';

const [, , seed, dir] = process.argv;
assert.ok(dir && seed);
const name = 'local_wiring_probe';
const profile = join(dir,'samples.jsonl'), mirror = join(dir,'stream.jsonl');
const url = process.env.PULSE_CHECK_GRAFANA;
const live = url ? await tracer.GrafanaRecorder.create({url,dashboard:'Z3-pulse-loop'}) : new tracer.JsonlRecorder({path:mirror});
const recorder = pairedRecorder(live,new tracer.JsonlRecorder({path:profile,costMode:'usage'}));
const failures: unknown[] = [];
let observer: JuncoFrontend | undefined, closeGraph: (()=>Promise<void>) | undefined;
try {
  observer = await JuncoFrontend.listen();
  const execution = await JuncoGraph.fromYaml(`graph:\n  nodes: { Probe: { kind: code } }\n  edges: [{ from: Probe, to: $sink, schema: {type: string} }]`,{
    cwd:seed, scheduler:()=>schedules.parallel(),tracer:observer,recorder,
    code:{Probe:c=>({state:new graph.nodes.Deterministic<TSchema,unknown>(async function*(){
      const view=c.recorder!.add_context(c.recorderNodeId ?? c.node);
      assert.equal(view.root,recorder.root);
      assert.equal(view,c.recorder!.add_context(c.recorderNodeId ?? c.node));
      view.record({kind:'probe',resource:'probe',edgeId:name,value:17,unit:'count:cases'});
      return 'recorded';
    },c.policy)})},
  });
  closeGraph = () => execution.graph.close();
  await execution.run();
  assert.deepEqual(execution.graph.result(execution.graph.sink.id),{_tag:'Some',value:'recorded'});
  const response=await fetch(observer.url+'/api/events?after=0');
  assert.ok(response.ok);
  const events=await response.json() as {kind:string;node?:string;phase?:string}[];
  assert.ok(events.some(e=>e.kind==='graph') && events.some(e=>e.kind==='run'&&e.phase==='start') && events.some(e=>e.kind==='activation'&&e.node==='Probe'));
  const stream=await fetch(observer.url+'/api/events/stream');
  const reader=stream.body!.getReader();
  try { assert.match(new TextDecoder().decode((await reader.read()).value),/id: \d+\ndata: \{/); }
  finally { await reader.cancel(); }
  await recorder.flush();
  for (const file of url ? [profile] : [profile,mirror]) {
    const probes=(await readFile(file,'utf8')).trim().split('\n').map(line=>JSON.parse(line)).filter(row=>row.measurement?.probe?.some((p:{edgeId:string})=>p.edgeId===name));
    assert.equal(probes.length,1); assert.equal(probes[0].node,'Probe'); assert.equal(probes[0].measurement.probe[0].value,17);
  }
  if (live instanceof tracer.GrafanaRecorder) {
    const query = new URL('/api/datasources/proxy/uid/junco-prometheus/api/v1/query',url);
    query.searchParams.set('query',`junco_probe_value{stream="${live.streamId}",node="Probe",edge_id="${name}"}`);
    const samples=await (await fetch(query)).json();
    assert.equal(samples.data.result.length,1); assert.equal(samples.data.result[0].value[1],'17');
    console.log(`Grafana probe verified: ${live.dashboardUrl}`);
  }
} catch (e) { failures.push(e); }
for(const close of [closeGraph,()=>recorder.close(),()=>observer?.close()])try{await close?.()}catch(e){failures.push(e)}
if(failures.length)throw new AggregateError(failures,'offline telemetry');
const closed: number[]=[];
const bad=(i:number):tracer.ProfileRecorder<string>=>({root:{},path:'',add_context(){return this},record(){throw Error('record '+i)},async flush(){throw Error('flush '+i)},async close(){closed.push(i);throw Error('close '+i)}});
const broken=pairedRecorder(bad(0),bad(1));
broken.record({kind:'probe',resource:'probe',edgeId:name,value:1});
await assert.rejects(broken.flush(),e=>e instanceof AggregateError && e.errors.length===4);
await assert.rejects(broken.close(),e=>e instanceof AggregateError && e.errors.length===6);
assert.deepEqual(closed,[0,1]);
console.log('Ephemeral frontend replay, SSE, node-scoped probes and both failing cleanup sinks verified');
