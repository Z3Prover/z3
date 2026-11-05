const assert = require("node:assert/strict");
const crypto = require("node:crypto");
const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const { execFileSync } = require("node:child_process");
const test = require("node:test");
const {
    producer, evidence, prepare, validatePayload, loadPayload, writeRunReport,
    filePatch, stageBundle, publishIssue,
} = require("./pulse-checker-repair.cjs");

const sha = "a".repeat(40);
const sourceSha = "b".repeat(40);
function payload(overrides = {}) {
    return JSON.stringify({
        base_sha: sha, source_sha: sourceSha, status: "verified",
        summary: "Check a missing rewrite with its semantic side conditions.",
        report: "One arithmetic rewrite improved from PARTIAL to ACCEPT; other families excluded.",
        validation_log: "Full verification and native tests passed.",
        commands: [{
            command: "pwsh -File fstar/tools/build_ocaml_checker.ps1 -RunTests",
            exit_code: 0, phase: "final",
        }],
        files: [{ path: "fstar/Z3Repair.fst", content: "module Z3Repair\n" }],
        ...overrides,
    });
}

function fixture(t) {
    const directory = fs.mkdtempSync(path.join(os.tmpdir(), "pulse-repair-test-"));
    t.after(() => fs.rmSync(directory, { recursive: true }));
    const run = {
        id: 42, run_attempt: 2, status: "completed", conclusion: "failure",
        path: ".github/workflows/pulse-checker-regressions.yml", head_sha: sourceSha,
        run_started_at: "2026-10-25T10:00:00Z",
        repository: { full_name: "Z3Prover/z3" },
        html_url: "https://github.com/Z3Prover/z3/actions/runs/42",
    };
    const reports = [
        { id: 10, name: "pulse-checker-report-42-2", expired: false },
        { id: 11, name: "pulse-checker-cherry-report-42-2", expired: false },
        { id: 12, name: "pulse-checker-report-42-1", expired: false },
        { id: 13, name: "pulse-checker-report-42-2", expired: true },
        { id: 14, name: "pulse-checker-report-999-2", expired: false },
        { id: 15, name: "pulse-checker-ocaml-linux-x86_64", expired: false },
    ];
    const issues = [], existing = [], outputs = [], summaries = [], failures = [];
    const args = {
        github: {
            rest: {
                actions: {
                    getWorkflowRun: async () => ({ data: run }),
                    listWorkflowRunArtifacts() {},
                    listJobsForWorkflowRunAttempt() {},
                    getArtifact: async () => ({ data: {
                        id: 77, name: "pulse-checker-repair-99-1",
                        expired: false, workflow_run: { id: 99 },
                    } }),
                },
                search: { issuesAndPullRequests: async () => ({ data: {
                    items: existing, incomplete_results: false,
                } }) },
                repos: { getContent: async () => {
                    const error = new Error("New source");
                    error.status = 404;
                    throw error;
                } },
                issues: { create: async issue => {
                    issues.push(issue);
                    return { data: { html_url: "https://github.com/Z3Prover/z3/issues/123" } };
                } },
            },
            paginate: async method => method === args.github.rest.actions.listWorkflowRunArtifacts
                ? reports : [{ name: "build", conclusion: "failure", steps: [] }],
        },
        context: {
            repo: { owner: "Z3Prover", repo: "z3" },
            payload: { workflow_run: { id: 42, run_attempt: 2 } },
            serverUrl: "https://github.com", runId: 99, runAttempt: 1,
        },
        core: {
            info() {}, setOutput: (...output) => outputs.push(output),
            setFailed: message => failures.push(message),
            summary: { addRaw(text) {
                summaries.push(text);
                return { write: async () => {} };
            } },
        },
        directory: path.join(directory, "bundle"), baseSha: sha,
        payload: payload(), artifactId: 77,
    };
    return { args, run, reports, issues, existing, outputs, summaries, failures, directory };
}

function candidate(args, text = args.payload) {
    fs.mkdirSync(args.directory, { recursive: true });
    const filename = path.join(args.directory, "payload.json");
    fs.writeFileSync(filename, text);
    const output = { items: [{
        type: "publish_pulse_repair",
        payload_sha256: crypto.createHash("sha256").update(text).digest("hex"),
    }], errors: [] };
    const outputFile = path.join(args.directory, "agent_output.json");
    fs.writeFileSync(outputFile, JSON.stringify(output));
    return { ...args, filename, output, outputFile,
        reportDirectory: path.join(args.directory, "analysis") };
}

function workflowScript(name) {
    const source = fs.readFileSync(path.join(__dirname, "..", "workflows", "pulse-checker-repair.md"), "utf8");
    const lines = source.split(`- name: ${name}`)[1].split(/\r?\n/);
    const start = lines.findIndex(line => line.trim() === "script: |");
    const indent = lines[start].match(/^ */)[0].length + 2;
    const script = [];
    for (const line of lines.slice(start + 1)) {
        if (line.trim() && !line.startsWith(" ".repeat(indent))) break;
        script.push(line.slice(indent));
    }
    return script.join("\n");
}

test("evidence selects only unexpired reports from the exact run and attempt", async t => {
    const { args, run } = fixture(t);
    assert.deepEqual((await evidence({ ...args, run })).map(item => item.id), [10, 11]);
});

test("build reports from an earlier attempt cannot substitute for a missing current report", async t => {
    const { args, run, reports } = fixture(t);
    run.path = ".github/workflows/pulse-checker-build.yml";
    reports.length = 0;
    reports.push({
        id: 20, name: "pulse-checker-build-report", expired: false,
        created_at: "2026-10-24T10:00:00Z",
    });
    assert.deepEqual(await evidence({ ...args, run }), []);
    reports.push({
        id: 21, name: "pulse-checker-build-report", expired: false,
        created_at: "2026-10-25T10:01:00Z",
    });
    assert.deepEqual((await evidence({ ...args, run })).map(item => item.id), [21]);
    delete run.run_started_at;
    await assert.rejects(evidence({ ...args, run }), /start time/);
});

test("invalid, unrelated, unfinished and advanced producers fail closed", async t => {
    for (const change of [
        { id: 43 }, { path: ".github/workflows/nightly.yml" }, { status: "in_progress" },
        { head_sha: "master" }, { run_attempt: 3 },
        { repository: { full_name: "contributor/z3" } },
    ]) {
        const { args, run } = fixture(t);
        Object.assign(run, change);
        await assert.rejects(producer(args));
    }
});

test("manual dispatch resolves and validates the supplied producer", async t => {
    const { args } = fixture(t);
    args.context.payload = { inputs: { run_id: "42" } };
    assert.equal((await producer(args)).id, 42);
    for (const run_id of ["42;echo bad", "", "0", "9007199254740993"]) {
        args.context.payload.inputs.run_id = run_id;
        await assert.rejects(producer(args));
    }
});

test("preparation includes job failures and marks successful regression runs actionable", async t => {
    const { args, run, outputs } = fixture(t);
    run.conclusion = "success";
    await prepare(args);
    const context = JSON.parse(fs.readFileSync(path.join(args.directory, "context.json")));
    assert.equal(context.base_sha, sha);
    assert.equal(context.actionable, true);
    assert.equal(context.jobs[0].conclusion, "failure");
    assert.ok(outputs.some(([key, value]) => key === "artifact-ids" && value === "10,11"));
});

test("github-script preparation supports wrapped require without require.resolve", async t => {
    const { args, directory } = fixture(t);
    const script = workflowScript("Prepare exact producer attempt and evidence index");
    const temporary = path.join(directory, "runner-temp");
    fs.mkdirSync(path.join(temporary, "gh-aw"), { recursive: true });
    const wrappedRequire = name => name === "./.github/scripts/pulse-checker-repair.cjs"
        ? { prepare: request => prepare({ ...request, directory: args.directory }) }
        : require(name);
    const AsyncFunction = Object.getPrototypeOf(async function() {}).constructor;
    await new AsyncFunction("require", "process", "github", "context", "core", script)(
        wrappedRequire, { env: {
            GITHUB_WORKSPACE: path.resolve(__dirname, "..", ".."),
            RUNNER_TEMP: temporary, TRUSTED_SHA: sha,
        } }, args.github, args.context, args.core);
    assert.equal(fs.readFileSync(path.join(temporary, "gh-aw", "pulse-checker-repair.cjs"), "utf8"),
        fs.readFileSync(path.join(__dirname, "pulse-checker-repair.cjs"), "utf8"));
    assert.equal(JSON.parse(fs.readFileSync(path.join(args.directory, "context.json"))).base_sha, sha);
});

test("successful builds and already published attempts do not start repair work", async t => {
    for (const mode of ["build", "duplicate"]) {
        const { args, run, existing } = fixture(t);
        if (mode === "build") {
            run.path = ".github/workflows/pulse-checker-build.yml";
            run.conclusion = "success";
        } else {
            existing.push({ user: { type: "Bot" }, body:
                "<!-- pulse-checker-repair:42:2 -->\n<!-- gh-aw-workflow-id: pulse-checker-repair -->" });
        }
        await prepare(args);
        const context = JSON.parse(fs.readFileSync(path.join(args.directory, "context.json")));
        assert.equal(context.actionable, false);
    }
});

test("missing reports remain explicit and ambiguous or incomplete API results fail", async t => {
    const { args, run, reports } = fixture(t);
    reports.length = 0;
    await prepare(args);
    assert.equal(JSON.parse(fs.readFileSync(path.join(args.directory, "context.json"))).missing_reports, true);
    reports.push(
        { id: 10, name: "pulse-checker-report-42-2" },
        { id: 11, name: "pulse-checker-report-42-2" },
    );
    await assert.rejects(evidence({ ...args, run }), /Ambiguous/);
    args.github.rest.search.issuesAndPullRequests = async () => ({ data: {
        incomplete_results: true, items: [],
    } });
    await assert.rejects(prepare(args), /incomplete/);
});

test("payload validation rejects escaping paths, duplicates and misleading verified statuses", () => {
    for (const filename of [
        "../Z3.fst", "fstar/../Z3.fst", "fstar/Z3..fst", "fstar\\Z3.fst",
        ".github/workflows/fix.yml", "src/smt/theory.cpp", "fstar/tools/evil.py",
    ])
        assert.throws(() => validatePayload(payload({
            files: [{ path: filename, content: "bad" }],
        }), sha));
    const file = { path: "fstar/Z3Repair.fst", content: "module Z3Repair\n" };
    for (const changes of [
        { base_sha: sourceSha }, { source_sha: "master" }, { status: "success" },
        { files: [file, file] }, { files: [] }, { commands: [] },
        { commands: [{ command: "verify", exit_code: 1, phase: "final" }] },
        { commands: [{ command: "verify", exit_code: "0" }] },
        { commands: [{ command: "verify", exit_code: 0, phase: "baseline" }] },
        { status: "no-fix" }, { report: "" },
        { files: [{ ...file, content: "x".repeat(512 * 1024 + 1) }] },
    ])
        assert.throws(() => validatePayload(payload(changes), sha));
    assert.equal(validatePayload(payload({
        source_sha: null, status: "no-fix", files: [], commands: [],
    }), sha).status, "no-fix");
});

test("a verified fix preserves failing baseline and exploratory command evidence", () => {
    const commands = [
        { command: "reproduce-original", exit_code: 1, phase: "baseline" },
        { command: "check-first-attempt", exit_code: 1, phase: "exploratory" },
        { command: "check-final-fix", exit_code: 0, phase: "final" },
    ];
    assert.equal(validatePayload(payload({ commands }), sha).status, "verified");
});

test("large repair sources cross the artifact boundary with only a compact tool receipt", async t => {
    const { args, summaries, failures, issues } = fixture(t);
    const text = payload({
        files: [{ path: "fstar/Z3Repair.fst", content: "module Z3Repair\n" + "let x = 0\n".repeat(6000) }],
    });
    assert.ok(Buffer.byteLength(text) > 10240);
    const request = candidate(args, text);
    assert.ok(Buffer.byteLength(JSON.stringify(request.output.items[0])) < 10240);
    await writeRunReport(request);
    assert.deepEqual(failures, []);
    const artifactPayload = loadPayload({
        ...request, filename: path.join(request.reportDirectory, "payload.json"),
    });
    assert.equal(artifactPayload, text);
    await stageBundle({ ...args, directory: path.join(args.directory, "final-bundle"), payload: artifactPayload });
    await publishIssue({ ...args, payload: artifactPayload });
    assert.equal(issues.length, 1);
    assert.ok(summaries.some(text => text.includes("Investigation and rule changes")));
    assert.ok(summaries.some(text => text.includes("https://github.com/Z3Prover/z3/issues/123")));
});

test("candidate transport rejects missing, duplicate, malformed and mismatched digests", t => {
    for (const mode of ["missing", "duplicate", "malformed", "mismatch", "oversized", "wrong-base"]) {
        const { args } = fixture(t);
        const request = candidate(args);
        if (mode === "missing") request.output.items.length = 0;
        if (mode === "duplicate") request.output.items.push(request.output.items[0]);
        if (mode === "malformed") request.output.items[0].payload_sha256 = "../payload.json";
        if (mode === "mismatch") fs.appendFileSync(request.filename, "\n");
        if (mode === "oversized") fs.writeFileSync(request.filename, "x".repeat(3 * 1024 * 1024 + 1));
        if (mode === "wrong-base") request.baseSha = sourceSha;
        assert.throws(() => loadPayload(request));
    }
});

test("an explicit no-op still produces a retained run report without a candidate", async t => {
    const { args, summaries, failures } = fixture(t);
    const request = candidate(args);
    fs.unlinkSync(request.filename);
    fs.writeFileSync(request.outputFile, JSON.stringify({ items: [{
        type: "noop", message: "Cancelled producer; no reports or new proof-rule evidence.",
    }] }));
    await writeRunReport(request);
    assert.deepEqual(failures, []);
    assert.ok(summaries[0].includes("no issue requested"));
    assert.ok(summaries[0].includes("Cancelled producer"));
    assert.ok(fs.existsSync(path.join(request.reportDirectory, "report.md")));
    assert.equal(fs.existsSync(path.join(request.reportDirectory, "payload.json")), false);
});

test("empty outputs, failed tools and corrupted candidates fail visibly and retain a report", async t => {
    for (const mode of ["empty", "incomplete", "corrupt", "mixed", "missing-output"]) {
        const { args, failures, summaries } = fixture(t);
        const request = candidate(args);
        if (mode === "empty") request.output.items.length = 0;
        if (mode === "incomplete")
            request.output.items = [{ type: "missing_tool", reason: "Publishing tool unavailable." }];
        if (mode === "corrupt") fs.appendFileSync(request.filename, "\n");
        if (mode === "mixed") request.output.items.push({ type: "noop", message: "No action" });
        fs.writeFileSync(request.outputFile, JSON.stringify(request.output));
        if (mode === "missing-output") fs.unlinkSync(request.outputFile);
        await writeRunReport(request);
        assert.equal(failures.length, 1);
        assert.ok(summaries[0].includes("Publication blocked"));
        assert.ok(fs.existsSync(path.join(request.reportDirectory, "report.md")));
        assert.equal(fs.existsSync(path.join(request.reportDirectory, "payload.json")), false);
    }
});

test("patches apply to existing, empty and new files with both newline conventions", t => {
    const { directory } = fixture(t);
    const examples = [
        { before: "module Old\n", after: "module New\n", added: false },
        { before: "module Old", after: "module New", added: false },
        { before: "module Old\r\n", after: "module New\r\n", added: false },
        { before: "", after: "module New\n", added: false },
        { before: "", after: "module New", added: true },
    ];
    for (const [index, example] of examples.entries()) {
        const root = path.join(directory, String(index));
        fs.mkdirSync(path.join(root, "fstar"), { recursive: true });
        if (!example.added)
            fs.writeFileSync(path.join(root, "fstar", "Z3Repair.fst"), example.before);
        fs.writeFileSync(path.join(root, "changes.patch"),
            filePatch("fstar/Z3Repair.fst", example.before, example.after, example.added));
        execFileSync("git", ["-c", "core.autocrlf=false", "apply", "--check", "changes.patch"], { cwd: root });
        execFileSync("git", ["-c", "core.autocrlf=false", "apply", "changes.patch"], { cwd: root });
        assert.equal(fs.readFileSync(path.join(root, "fstar", "Z3Repair.fst"), "utf8"), example.after);
    }
});

test("staging packages sources, reconstructs a patch and records hashes without creating an issue", async t => {
    const { args, issues } = fixture(t);
    args.github.rest.repos.getContent = async request => {
        assert.equal(request.ref, sha);
        return { data: { type: "file", encoding: "base64",
            content: Buffer.from("module Before\n").toString("base64") } };
    };
    await stageBundle(args);
    const manifest = JSON.parse(fs.readFileSync(path.join(args.directory, "manifest.json")));
    assert.equal(manifest.base_sha, sha);
    assert.equal(manifest.reported_source_sha, sourceSha);
    assert.equal(manifest.producer_attempt, 2);
    assert.equal(manifest.files[0].added, false);
    assert.match(manifest.files[0].before_sha256, /^[0-9a-f]{64}$/);
    assert.match(manifest.files[0].sha256, /^[0-9a-f]{64}$/);
    assert.equal(manifest.artifacts.length, 2);
    assert.equal(issues.length, 0);
    assert.ok(fs.readFileSync(path.join(args.directory, "changes.patch"), "utf8").includes("-module Before"));
    assert.equal(fs.readFileSync(path.join(args.directory, "sources", "fstar", "Z3Repair.fst"), "utf8"),
        "module Z3Repair\n");
});

test("source fetch failures and unchanged sources are not disguised as additions", async t => {
    for (const mode of ["unavailable", "unchanged", "symlink"]) {
        const { args } = fixture(t);
        args.github.rest.repos.getContent = async () => {
            if (mode === "unavailable") throw Object.assign(new Error("Forbidden"), { status: 403 });
            return { data: {
                type: mode === "symlink" ? "symlink" : "file",
                encoding: "base64", content: Buffer.from("module Z3Repair\n").toString("base64"),
            } };
        };
        await assert.rejects(stageBundle(args));
    }
});

test("publication links the uploaded artifact and original evidence with integration instructions", async t => {
    const { args, issues } = fixture(t);
    await publishIssue(args);
    assert.equal(issues.length, 1);
    assert.equal(issues[0].title, "[Pulse checker repair] Run 42 attempt 2");
    assert.ok(issues[0].body.includes("actions/runs/99/artifacts/77"));
    assert.ok(issues[0].body.includes("actions/runs/42/artifacts/10"));
    assert.ok(issues[0].body.includes("git apply --check changes.patch"));
    assert.ok(issues[0].body.includes("Assign this issue to Copilot"));
    assert.ok(issues[0].body.includes("Agent-reported validation"));
    assert.ok(issues[0].body.includes("<!-- pulse-checker-repair:42:2 -->"));
});

test("github-script publication preserves the prototype-backed repository context", async t => {
    const { args, run, directory, issues } = fixture(t);
    const request = candidate(args);
    const temporary = path.join(directory, "runner-temp");
    const analysis = path.join(temporary, "pulse-repair-analysis");
    fs.mkdirSync(analysis, { recursive: true });
    fs.copyFileSync(request.filename, path.join(analysis, "payload.json"));
    const { repo, runAttempt, ...fields } = args.context;
    const context = Object.assign(Object.create({ get repo() { return repo; } }), fields);
    args.github.rest.actions.getWorkflowRun = async request => {
        assert.equal(request.owner, repo.owner);
        assert.equal(request.repo, repo.repo);
        return { data: run };
    };
    const wrappedRequire = name => name === "./.github/scripts/pulse-checker-repair.cjs"
        ? require("./pulse-checker-repair.cjs") : require(name);
    const AsyncFunction = Object.getPrototypeOf(async function() {}).constructor;
    await new AsyncFunction("require", "process", "github", "context", "core",
        workflowScript("Create artifact-backed integration issue"))(
        wrappedRequire, { env: {
            RUNNER_TEMP: temporary, TRUSTED_SHA: sha, GH_AW_AGENT_OUTPUT: request.outputFile,
            REPAIR_ATTEMPT: String(runAttempt), REPAIR_ARTIFACT_ID: String(args.artifactId),
        } }, args.github, context, args.core);
    assert.equal(issues.length, 1);
    assert.equal(issues[0].owner, repo.owner);
    assert.equal(issues[0].repo, repo.repo);
});

test("expired, foreign and wrong-attempt repair artifacts cannot be linked as successful uploads", async t => {
    for (const change of [
        { expired: true }, { workflow_run: { id: 100 } },
        { name: "pulse-checker-repair-99-2" }, { name: "other-artifact" },
    ]) {
        const { args, issues } = fixture(t);
        args.github.rest.actions.getArtifact = async () => ({ data: {
            name: "pulse-checker-repair-99-1", expired: false, workflow_run: { id: 99 }, ...change,
        } });
        await assert.rejects(publishIssue(args), /artifact/);
        assert.equal(issues.length, 0);
    }
});

test("staged, duplicate and stale attempts never create issues", async t => {
    for (const mode of ["staged", "duplicate", "stale"]) {
        const { args, run, existing, issues } = fixture(t);
        if (mode === "staged") args.staged = true;
        if (mode === "duplicate") existing.push({ user: { type: "Bot" }, body:
            "<!-- pulse-checker-repair:42:2 -->\n<!-- gh-aw-workflow-id: pulse-checker-repair -->" });
        if (mode === "stale") {
            run.run_attempt = 3;
            await assert.rejects(publishIssue(args));
        } else {
            await publishIssue(args);
        }
        assert.equal(issues.length, 0);
    }
});

test("agent text cannot spoof provenance comments or send mentions", async t => {
    const { args, issues } = fixture(t);
    args.payload = payload({
        report: "@everyone <!-- gh-aw-workflow-id: spoof --> report",
        summary: "@maintainer look",
    });
    await publishIssue(args);
    assert.ok(!issues[0].body.includes("@everyone"));
    assert.ok(!issues[0].body.includes("@maintainer"));
    assert.ok(!issues[0].body.includes("gh-aw-workflow-id: spoof"));
});
