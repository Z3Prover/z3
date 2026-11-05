const crypto = require("node:crypto");
const fs = require("node:fs");
const path = require("node:path");

const profiles = {
    fstar: {
        label: "F*", title: "Fstar NFV PR audit", language: "fstar",
        filename: /^[A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)*\.fst$/,
        preview: "F* model",
        scope: "This is a scoped semantic source audit, not mechanized verification of the C++ implementation or the entire PR.",
    },
    vercors: {
        label: "VerCors", title: "VerCors C++ NFV PR audit", language: "cpp",
        filename: /^[A-Za-z][A-Za-z0-9_]*\.(?:cpp|hpp)$/,
        preview: "VerCors C++ audit sources",
        scope: "This verifies selected annotated C++ extracts within VerCors's supported semantics, not the complete C++ implementation or the entire PR. Source correspondence and environment assumptions remain explicit review obligations.",
    },
};

function validatePayload(text, expectedSha, profile) {
    if (typeof text !== "string" || Buffer.byteLength(text) > 256 * 1024)
        throw new Error("Audit payload exceeds 256 KiB or is not a string");
    const data = JSON.parse(text);
    if (data.head_sha !== expectedSha || !/^[0-9a-f]{40}$/.test(expectedSha))
        throw new Error("Audit revision does not match the triggering head");
    if (!["proved", "counterexample", "inconclusive"].includes(data.verdict))
        throw new Error("Invalid audit verdict");
    for (const key of ["summary", "report", "verification_log"]) {
        if (typeof data[key] !== "string" || !data[key].trim())
            throw new Error(`Missing audit ${key}`);
    }
    if (data.summary.length > 2000 || data.report.length > 48000)
        throw new Error("Audit summary or report exceeds its limit");
    if (!Array.isArray(data.files) || data.files.length > 8)
        throw new Error("Expected at most eight proof modules");
    const names = new Set();
    for (const file of data.files) {
        if (!file || typeof file.name !== "string" ||
            !profile.filename.test(file.name) ||
            names.has(file.name.toLowerCase()))
            throw new Error("Invalid or duplicate proof module filename");
        if (typeof file.content !== "string" || !file.content.trim() ||
            Buffer.byteLength(file.content) > 64 * 1024)
            throw new Error("Empty or oversized proof module");
        names.add(file.name.toLowerCase());
    }
    if (data.verdict !== "inconclusive" && data.files.length === 0)
        throw new Error("A conclusive audit requires proof sources");
    if (profile.language === "cpp" && data.verdict !== "inconclusive" &&
        !data.files.some(file => file.name.endsWith(".cpp")))
        throw new Error("A conclusive C++ audit requires a .cpp verification unit");
    return data;
}

async function resolvePullRequest(github, context) {
    if (context.eventName !== "workflow_dispatch")
        return context.payload.pull_request;
    const { pr_number, head_sha } = context.payload.inputs || {};
    if (!/^[1-9][0-9]*$/.test(pr_number) || !Number.isSafeInteger(Number(pr_number)) ||
        !/^[0-9a-f]{40}$/.test(head_sha))
        throw new Error("Manual audit requires a PR number and exact head SHA");
    const { data: pr } = await github.rest.pulls.get({
        ...context.repo, pull_number: Number(pr_number),
    });
    if (pr.state !== "open" || pr.base.ref !== "master" || pr.head.sha !== head_sha)
        throw new Error("Manual audit target is closed, stale, or not based on master");
    return pr;
}

async function publish({ github, context, core, payload, artifactDir, staged = false }, backend, profile) {
    const eventPr = await resolvePullRequest(github, context);
    if (!eventPr || !Number.isSafeInteger(eventPr.number) || eventPr.number < 1)
        throw new Error("Publication requires a triggering pull request");
    const data = validatePayload(payload, eventPr.head.sha, profile);
    const repo = context.repo;
    const { data: pr } = await github.rest.pulls.get({
        ...repo, pull_number: eventPr.number,
    });
    if (pr.state !== "open" || pr.head.sha !== eventPr.head.sha ||
        pr.head.ref !== eventPr.head.ref || pr.base.ref !== "master" ||
        pr.head.repo?.full_name !== eventPr.head.repo?.full_name) {
        core.info("Skipping stale or closed PR audit");
        return { status: "stale" };
    }
    const marker = `<!-- ${backend}-nfv-audit:${data.head_sha} -->`;
    const comments = await github.paginate(github.rest.issues.listComments, {
        ...repo, issue_number: pr.number, per_page: 100,
    });
    if (comments.some(comment => comment.user?.type === "Bot" &&
        comment.body?.includes(marker))) {
        core.info("Skipping an already published revision");
        return { status: "duplicate" };
    }
    const prefix = `${backend}/audits/pr-${pr.number}/${data.head_sha}/`;
    const files = [
        ...data.files,
        { name: "REPORT.md", content: data.report },
        { name: "verification.log", content: data.verification_log },
    ];
    const runUrl = `${context.serverUrl}/${repo.owner}/${repo.repo}/actions/runs/${context.runId}`;
    const manifest = {
        pull_request: pr.number, head_sha: data.head_sha,
        base_sha: eventPr.base.sha, path_prefix: prefix,
        verdict: data.verdict, run_url: runUrl,
        files: files.map(file => ({
            name: file.name,
            sha256: crypto.createHash("sha256").update(file.content).digest("hex"),
        })),
    };
    files.push({ name: "manifest.json", content: JSON.stringify(manifest, null, 2) + "\n" });
    fs.mkdirSync(artifactDir, { recursive: true });
    for (const file of files)
        fs.writeFileSync(path.join(artifactDir, file.name), file.content, { flag: "wx" });
    core.setOutput("artifact-path", artifactDir);

    const sameRepo = pr.head.repo.full_name.toLowerCase() ===
        `${repo.owner}/${repo.repo}`.toLowerCase();
    if (sameRepo && pr.head.ref === pr.base.ref)
        throw new Error("Refusing to modify the base branch");
    if (staged) {
        core.info(`Staged audit: ${sameRepo ? "commit" : "artifact only"} for ${prefix}`);
        return { status: "staged" };
    }
    let commitUrl;
    if (sameRepo) {
        // No PR checkout or force push: GitHub appends to exactly the audited head.
        const result = await github.graphql(`
          mutation($input: CreateCommitOnBranchInput!) {
            createCommitOnBranch(input: $input) { commit { url } }
          }`, {
            input: {
                branch: {
                    repositoryNameWithOwner: `${repo.owner}/${repo.repo}`,
                    branchName: pr.head.ref,
                },
                expectedHeadOid: data.head_sha,
                message: { headline: `Add ${profile.label} NFV audit for #${pr.number} at ${data.head_sha.slice(0, 12)}` },
                fileChanges: {
                    additions: files.map(file => ({
                        path: prefix + file.name,
                        contents: Buffer.from(file.content).toString("base64"),
                    })),
                },
            },
        });
        commitUrl = result.createCommitOnBranch.commit.url;
    }
    const evidence = commitUrl
        ? `Audit sources, report, and verification log: ${commitUrl}`
        : "Fork PR: no branch writes were attempted. Download the audit sources, report, and log from the run artifacts.";
    const summary = data.summary.replace(/@/g, "@\u200b");
    const modelCharacters = Array.from(data.files.map(file => file.content).join("\n\n"));
    const preview = modelCharacters.slice(0, 5000).join("");
    const fenceLength = Math.max(3, ...Array.from(preview.matchAll(/`+/g), match => match[0].length + 1));
    const fence = "`".repeat(fenceLength);
    const modelPreview = modelCharacters.length ? [
        "", `### ${profile.preview}`, "", `${fence}${profile.language}`, preview, fence,
        ...(modelCharacters.length > 5000
            ? ["", "Preview truncated to 5,000 characters; full sources are linked above."]
            : []),
    ] : [];
    const body = [
        marker, `## ${profile.label} NFV audit: ${data.verdict}`,
        `Audited head: \`${data.head_sha}\``, "", summary, "", evidence,
        `[Workflow run and downloadable evidence (30-day retention)](${runUrl})`,
        ...modelPreview, "",
        profile.scope,
        "An inconclusive result or an unproved obligation is not evidence of correctness.",
        "", `Generated by [${profile.title}](${runUrl}).`,
        `<!-- gh-aw-workflow-id: ${backend}-nfv-audit -->`,
    ].join("\n");
    await github.rest.issues.createComment({
        ...repo, issue_number: pr.number, body,
    });
    return { status: sameRepo ? "committed" : "artifact", commitUrl };
}

function forBackend(backend) {
    if (!Object.hasOwn(profiles, backend))
        throw new Error("Unknown formal audit backend");
    const profile = profiles[backend];
    return {
        publish: args => publish(args, backend, profile),
        validatePayload: (text, expectedSha) => validatePayload(text, expectedSha, profile),
    };
}

module.exports = { forBackend, resolvePullRequest };
