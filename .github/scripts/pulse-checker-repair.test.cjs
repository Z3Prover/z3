const assert = require("node:assert/strict");
const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const { execFileSync } = require("node:child_process");
const test = require("node:test");
const {
    producer, evidence, prepare, validatePayload, filePatch, stageBundle, publishIssue,
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
    const issues = [], existing = [], outputs = [];
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
        core: { info() {}, setOutput: (...output) => outputs.push(output) },
        directory: path.join(directory, "bundle"), baseSha: sha,
        payload: payload(), artifactId: 77,
    };
    return { args, run, reports, issues, existing, outputs, directory };
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
