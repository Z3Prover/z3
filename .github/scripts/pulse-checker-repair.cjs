const crypto = require("node:crypto");
const fs = require("node:fs");
const path = require("node:path");

const BUILD = ".github/workflows/pulse-checker-build.yml";
const REGRESSIONS = ".github/workflows/pulse-checker-regressions.yml";
const WORKFLOW = "pulse-checker-repair";
const allowedFile = /^fstar\/(?:[A-Z][A-Za-z0-9_.]*\.(?:fst|fsti)|ocaml_runtime\/[A-Za-z0-9_]+\.ml|tools\/(?:checker_modules\.json|build_(?:ocaml|cherry)_checker\.ps1|test_[A-Za-z0-9_]+\.(?:py|ml))|benchmarks\/repair\/[A-Za-z0-9_-]+\.smt2)$/;

function positiveInteger(value) {
    const number = Number(value);
    if (!/^[1-9][0-9]*$/.test(String(value)) || !Number.isSafeInteger(number))
        throw new Error("Expected a positive safe integer");
    return number;
}

function marker(run) {
    return `<!-- pulse-checker-repair:${run.id}:${run.run_attempt} -->`;
}

async function producer({ github, context }) {
    const event = context.payload.workflow_run;
    const id = positiveInteger(event?.id ?? context.payload.inputs?.run_id);
    const { data: run } = await github.rest.actions.getWorkflowRun({
        ...context.repo, run_id: id,
    });
    if (run.id !== id || run.status !== "completed" ||
        ![BUILD, REGRESSIONS].includes(run.path?.split("@")[0]) ||
        !/^[0-9a-f]{40}$/.test(run.head_sha) ||
        run.repository?.full_name?.toLowerCase() !==
            `${context.repo.owner}/${context.repo.repo}`.toLowerCase())
        throw new Error("Expected a completed Pulse workflow run in this repository");
    positiveInteger(run.run_attempt);
    if (event && run.run_attempt !== event.run_attempt)
        throw new Error("Producer has advanced to another attempt; refusing mixed evidence");
    return run;
}

async function evidence({ github, context, run }) {
    const artifacts = await github.paginate(github.rest.actions.listWorkflowRunArtifacts, {
        ...context.repo, run_id: run.id, per_page: 100,
    });
    const names = run.path.split("@")[0] === BUILD
        ? ["pulse-checker-build-report"]
        : [
            `pulse-checker-report-${run.id}-${run.run_attempt}`,
            `pulse-checker-cherry-report-${run.id}-${run.run_attempt}`,
        ];
    const build = run.path.split("@")[0] === BUILD;
    const attemptStart = Date.parse(run.run_started_at);
    if (build && !Number.isFinite(attemptStart))
        throw new Error("Missing build attempt start time");
    const selected = artifacts.filter(item => names.includes(item.name) && !item.expired &&
        (!build || Date.parse(item.created_at) >= attemptStart));
    if (new Set(selected.map(item => item.name)).size !== selected.length)
        throw new Error("Ambiguous producer report artifacts");
    const base = `${context.serverUrl}/${context.repo.owner}/${context.repo.repo}/actions/runs/${run.id}`;
    return selected.map(item => ({
        id: positiveInteger(item.id), name: item.name, size_in_bytes: item.size_in_bytes,
        url: `${base}/artifacts/${item.id}`,
    }));
}

async function existingIssue({ github, context, run }) {
    const result = await github.rest.search.issuesAndPullRequests({
        q: `repo:${context.repo.owner}/${context.repo.repo} is:issue "pulse-checker-repair:${run.id}:${run.run_attempt}" in:body`,
        per_page: 100,
    });
    if (result.data.incomplete_results)
        throw new Error("Issue duplicate search was incomplete");
    return result.data.items.find(item => item.user?.type === "Bot" &&
        item.body?.includes(marker(run)) &&
        item.body.includes(`<!-- gh-aw-workflow-id: ${WORKFLOW} -->`));
}

async function prepare({ github, context, core, directory, baseSha }) {
    if (!/^[0-9a-f]{40}$/.test(baseSha))
        throw new Error("Missing trusted checkout revision");
    const args = { github, context };
    const run = await producer(args);
    const duplicate = await existingIssue({ ...args, run });
    const artifacts = await evidence({ ...args, run });
    const jobs = await github.paginate(github.rest.actions.listJobsForWorkflowRunAttempt, {
        ...context.repo, run_id: run.id, attempt_number: run.run_attempt, per_page: 100,
    });
    const actionable = !(run.path.split("@")[0] === BUILD && run.conclusion === "success") &&
        !duplicate;
    fs.mkdirSync(directory, { recursive: true });
    fs.writeFileSync(path.join(directory, "context.json"), JSON.stringify({
        base_sha: baseSha, producer: run, artifacts,
        jobs: jobs.map(({ name, conclusion, html_url, steps }) => ({
            name, conclusion, html_url, steps,
        })),
        duplicate_issue: duplicate?.html_url ?? null,
        actionable,
        missing_reports: artifacts.length === 0,
    }, null, 2) + "\n");
    core.setOutput("run-id", String(run.id));
    core.setOutput("attempt", String(run.run_attempt));
    core.setOutput("artifact-ids", artifacts.map(item => item.id).join(","));
    core.setOutput("actionable", String(actionable));
    core.setOutput("conclusion", run.conclusion);
}

function validatePayload(text, baseSha) {
    if (typeof text !== "string" || Buffer.byteLength(text) > 3 * 1024 * 1024)
        throw new Error("Repair payload must be a string of at most 3 MiB");
    const data = JSON.parse(text);
    if (!/^[0-9a-f]{40}$/.test(baseSha) || data.base_sha !== baseSha)
        throw new Error("Repair base does not match the trusted checkout");
    if (data.source_sha !== null && !/^[0-9a-f]{40}$/.test(data.source_sha))
        throw new Error("Expected the reported checker source SHA or null");
    if (!["verified", "incomplete", "no-fix"].includes(data.status))
        throw new Error("Invalid repair validation status");
    for (const [field, limit] of [
        ["summary", 2000], ["report", 40000], ["validation_log", 512 * 1024],
    ]) {
        if (typeof data[field] !== "string" || !data[field].trim() ||
            Buffer.byteLength(data[field]) > limit)
            throw new Error(`Missing or oversized repair ${field}`);
    }
    if (!Array.isArray(data.commands) || data.commands.length > 100 ||
        data.commands.some(item => !item || typeof item.command !== "string" ||
            !item.command.trim() || item.command.length > 4000 ||
            !Number.isInteger(item.exit_code) ||
            !["baseline", "exploratory", "final"].includes(item.phase)))
        throw new Error("Invalid validation command records");
    if (!Array.isArray(data.files) || data.files.length > 16)
        throw new Error("Expected at most sixteen changed source files");
    const finalCommands = data.commands.filter(item => item.phase === "final");
    if ((data.status === "verified" && (!data.files.length || !finalCommands.length ||
        finalCommands.some(item => item.exit_code !== 0))) ||
        (data.status === "no-fix" && data.files.length))
        throw new Error("Repair status disagrees with its files or validation commands");
    const names = new Set();
    for (const file of data.files) {
        if (!file || typeof file.path !== "string" || !allowedFile.test(file.path) ||
            file.path.includes("..") || names.has(file.path.toLowerCase()) ||
            typeof file.content !== "string" || !file.content.trim() ||
            file.content.includes("\0") || Buffer.byteLength(file.content) > 512 * 1024)
            throw new Error("Invalid, duplicate, or oversized repair source file");
        names.add(file.path.toLowerCase());
    }
    return data;
}

function patchLines(text, prefix) {
    if (!text) return [];
    const lines = text.split("\n");
    if (lines.at(-1) === "") lines.pop();
    const result = lines.map(line => prefix + line);
    if (!text.endsWith("\n")) result.push("\\ No newline at end of file");
    return result;
}

function filePatch(filename, before, after, added) {
    const oldLines = patchLines(before, "-");
    const newLines = patchLines(after, "+");
    const count = text => text ? text.split("\n").length - Number(text.endsWith("\n")) : 0;
    const oldCount = count(before), newCount = count(after);
    return [
        `diff --git a/${filename} b/${filename}`,
        ...(added ? ["new file mode 100644"] : []),
        `--- ${added ? "/dev/null" : `a/${filename}`}`,
        `+++ b/${filename}`,
        `@@ -${oldCount ? 1 : 0},${oldCount} +${newCount ? 1 : 0},${newCount} @@`,
        ...oldLines, ...newLines, "",
    ].join("\n");
}

async function stageBundle({ github, context, core, payload, baseSha, directory }) {
    const data = validatePayload(payload, baseSha);
    const run = await producer({ github, context });
    if (run.path.split("@")[0] === BUILD && run.conclusion === "success")
        throw new Error("Successful builds are analyzed through their regression run");
    if (await existingIssue({ github, context, run })) {
        core.info("Skipping an already published producer attempt");
        return;
    }
    const artifacts = await evidence({ github, context, run });
    const files = [];
    let patch = "";
    for (const file of data.files) {
        let before = "", added = false;
        try {
            const { data: original } = await github.rest.repos.getContent({
                ...context.repo, path: file.path, ref: baseSha,
            });
            if (original.type !== "file" || original.encoding !== "base64" ||
                typeof original.content !== "string")
                throw new Error("Expected a regular source file with inline contents");
            before = Buffer.from(original.content, "base64").toString("utf8");
        } catch (error) {
            if (error.status !== 404) throw error;
            added = true;
        }
        if (before === file.content)
            throw new Error(`Unchanged source included in repair: ${file.path}`);
        patch += filePatch(file.path, before, file.content, added);
        const target = path.join(directory, "sources", file.path);
        fs.mkdirSync(path.dirname(target), { recursive: true });
        fs.writeFileSync(target, file.content, { flag: "wx" });
        files.push({
            path: file.path, added,
            before_sha256: added ? null : crypto.createHash("sha256").update(before).digest("hex"),
            sha256: crypto.createHash("sha256").update(file.content).digest("hex"),
        });
    }
    fs.mkdirSync(directory, { recursive: true });
    const manifest = {
        base_sha: baseSha, reported_source_sha: data.source_sha,
        producer_run: run.id, producer_attempt: run.run_attempt,
        status: data.status, artifacts, files,
        commands: data.commands,
        patch_sha256: crypto.createHash("sha256").update(patch).digest("hex"),
    };
    for (const [name, content] of [
        ["manifest.json", JSON.stringify(manifest, null, 2) + "\n"],
        ["report.md", data.report], ["validation.log", data.validation_log],
        ["changes.patch", patch],
    ])
        fs.writeFileSync(path.join(directory, name), content, { flag: "wx" });
    core.setOutput("artifact-path", directory);
}

async function publishIssue({ github, context, core, payload, baseSha, artifactId, staged = false }) {
    const data = validatePayload(payload, baseSha);
    const run = await producer({ github, context });
    if (await existingIssue({ github, context, run })) {
        core.info("Skipping an already published producer attempt");
        return;
    }
    const id = positiveInteger(artifactId);
    const { data: artifact } = await github.rest.actions.getArtifact({
        ...context.repo, artifact_id: id,
    });
    if (artifact.expired || artifact.workflow_run?.id !== Number(context.runId) ||
        artifact.name !== `pulse-checker-repair-${context.runId}-${context.runAttempt}`)
        throw new Error("Repair artifact is not from this analysis run and attempt");
    const artifacts = await evidence({ github, context, run });
    const runUrl = `${context.serverUrl}/${context.repo.owner}/${context.repo.repo}/actions/runs/${context.runId}`;
    const text = value => value.replace(/@/g, "@\u200b").replace(/<!--[\s\S]*?-->/g, "");
    const body = [
        marker(run), "## Pulse checker integration handoff", "",
        text(data.summary), "",
        `**Agent-reported validation:** ${data.status}. Revalidate independently during integration.`,
        `**Patch base:** \`${baseSha}\``,
        `**Reported checker source:** ${data.source_sha ? `\`${data.source_sha}\`` : "unavailable; see report"}`,
        `[Producer run, attempt ${run.run_attempt}](${run.html_url})`,
        `[Repair sources, portable patch, manifest and validation log](${runUrl}/artifacts/${id})`,
        "Repair artifacts expire after 30 days; download them before expiration.",
        "", "### Original evidence",
        ...(artifacts.length ? artifacts.map(item => `- [${item.name}](${item.url})`) :
            ["No unexpired report artifacts were available; consult the producer logs."]),
        "", "### Updates and evidence", "", text(data.report), "",
        "### Copilot integration instructions", "",
        "Assign this issue to Copilot when ready. Download the repair artifact and inspect its manifest and sources. " +
            "For a nonempty patch, check out its recorded base, run `git apply --check changes.patch`, " +
            "then apply it. Rebase onto current master and review every change before integration.",
        "Run fresh F*/Pulse verification, native bridge/CLI tests, and the listed benchmark reproducers, " +
            "including negative/malformed-proof tests. Preserve soundness and all unresolved obligations. " +
            "Incomplete candidates are not ready-to-merge fixes; complete their missing checks first. " +
            "A no-fix report has no code patch to apply. This workflow did not push a branch or open a PR.",
        "", `Generated by [Pulse checker repair](${runUrl}).`,
        `<!-- gh-aw-workflow-id: ${WORKFLOW} -->`,
        `<!-- gh-aw-run-id: ${context.runId} -->`,
    ].join("\n");
    if (staged) {
        core.info("Staged repair handoff: no issue created");
        return;
    }
    const { data: issue } = await github.rest.issues.create({
        ...context.repo, title: `[Pulse checker repair] Run ${run.id} attempt ${run.run_attempt}`, body,
    });
    core.setOutput("issue-url", issue.html_url);
}

module.exports = {
    producer, evidence, prepare, validatePayload, filePatch, stageBundle, publishIssue,
};
