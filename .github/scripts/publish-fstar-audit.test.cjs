const assert = require("node:assert/strict");
const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const test = require("node:test");
const { publish, validatePayload } = require("./publish-fstar-audit.cjs");

const sha = "a".repeat(40);
function payload(overrides = {}) {
    return JSON.stringify({
        head_sha: sha, verdict: "proved", summary: "One selected arithmetic obligation checked.",
        report: "Scoped audit report.", verification_log: "Verifier exited 0.",
        files: [{ name: "PrAudit.fst", content: "module PrAudit\n" }], ...overrides,
    });
}

function fixture(t, overrides = {}) {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "fstar-nfv-test-"));
    t.after(() => fs.rmSync(dir, { recursive: true }));
    const pr = {
        number: 7, state: "open",
        head: { sha, ref: "feature", repo: { full_name: "Z3Prover/z3" } },
        base: { ref: "master", sha: "b".repeat(40) },
        ...overrides,
    };
    const commits = [], comments = [], outputs = [];
    const args = {
        context: {
            repo: { owner: "Z3Prover", repo: "z3" }, payload: { pull_request: pr },
            serverUrl: "https://github.com", runId: 99,
        },
        github: {
            rest: {
                pulls: { get: async () => ({ data: pr }) },
                issues: { listComments() {}, createComment: async item => comments.push(item) },
            },
            paginate: async () => [],
            graphql: async (query, variables) => {
                commits.push(variables.input);
                return { createCommitOnBranch: { commit: { url: "https://github.com/commit/audit" } } };
            },
        },
        core: { info() {}, setOutput: (...values) => outputs.push(values) },
        payload: payload(), artifactDir: path.join(dir, "artifact"),
    };
    return { args, pr, commits, comments, outputs };
}

test("same-repository publication appends only audit files at the exact head", async t => {
    const { args, commits, comments } = fixture(t);
    assert.equal((await publish(args)).status, "committed");
    assert.equal(commits.length, 1);
    assert.equal(commits[0].expectedHeadOid, sha);
    assert.equal(commits[0].branch.branchName, "feature");
    assert.equal(commits[0].fileChanges.additions.length, 4);
    for (const file of commits[0].fileChanges.additions)
        assert.ok(file.path.startsWith(`fstar/audits/pr-7/${sha}/`));
    const manifest = JSON.parse(fs.readFileSync(path.join(args.artifactDir, "manifest.json")));
    assert.equal(manifest.base_sha, "b".repeat(40));
    assert.equal(manifest.path_prefix, `fstar/audits/pr-7/${sha}/`);
    assert.equal(manifest.files.length, 3);
    assert.equal(comments.length, 1);
    assert.ok(comments[0].body.includes("https://github.com/commit/audit"));
    assert.ok(comments[0].body.includes("```fstar\nmodule PrAudit\n\n```"));
});

test("forks receive artifacts and a comment without any commit", async t => {
    const { args, commits, comments } = fixture(t, {
        head: { sha, ref: "feature", repo: { full_name: "contributor/z3" } },
    });
    assert.equal((await publish(args)).status, "artifact");
    assert.equal(commits.length, 0);
    assert.equal(comments.length, 1);
    assert.ok(fs.existsSync(path.join(args.artifactDir, "PrAudit.fst")));
    assert.ok(comments[0].body.includes("no branch writes"));
    assert.ok(comments[0].body.includes("```fstar\nmodule PrAudit\n\n```"));
});

test("model previews share a 5,000-character budget while preserving full sources", async t => {
    for (const lengths of [[4999], [5000], [5001], [3000, 3000]]) {
        const { args, comments } = fixture(t);
        const files = lengths.map((length, i) => {
            const prefix = `module PrAudit${i}\n// `;
            return { name: `PrAudit${i}.fst`, content: prefix + String(i).repeat(length - prefix.length) };
        });
        args.payload = payload({ files });
        await publish(args);
        const model = files.map(file => file.content).join("\n\n");
        const preview = model.slice(0, 5000);
        assert.ok(comments[0].body.includes(`\n\`\`\`fstar\n${preview}\n\`\`\`\n`));
        assert.equal(comments[0].body.includes("Preview truncated"), model.length > 5000);
        for (const file of files)
            assert.equal(fs.readFileSync(path.join(args.artifactDir, file.name), "utf8"), file.content);
    }
});

test("model previews preserve Unicode characters and contain embedded Markdown fences", async t => {
    const { args, comments } = fixture(t);
    const prefix = "module PrAudit\n(*\n```\n````\n</details>\n@everyone\n";
    const preview = prefix + "\u{1f642}".repeat(5000 - prefix.length);
    args.payload = payload({ files: [{ name: "PrAudit.fst", content: preview + "OMITTED *)" }] });
    await publish(args);
    assert.ok(comments[0].body.includes(`\n\`\`\`\`\`fstar\n${preview}\n\`\`\`\`\`\n`));
    assert.ok(!comments[0].body.includes("OMITTED"));
    assert.ok(comments[0].body.includes("Preview truncated"));
});

test("inconclusive audits without sources omit the model preview", async t => {
    const { args, comments } = fixture(t);
    args.payload = payload({ verdict: "inconclusive", files: [] });
    await publish(args);
    assert.equal(comments.length, 1);
    assert.ok(comments[0].body.includes("F* NFV audit: inconclusive"));
    assert.ok(!comments[0].body.includes("### F* model"));
    assert.ok(!comments[0].body.includes("Preview truncated"));
});

test("stale, closed, and duplicate audits do not publish", async t => {
    for (const state of ["stale", "closed", "duplicate"]) {
        const { args, pr, commits, comments, outputs } = fixture(t);
        if (state === "stale")
            args.github.rest.pulls.get = async () => ({ data: { ...pr, head: { ...pr.head, sha: "c".repeat(40) } } });
        else if (state === "closed")
            args.github.rest.pulls.get = async () => ({ data: { ...pr, state: "closed" } });
        else
            args.github.paginate = async () => [{
                user: { type: "Bot" }, body: `<!-- fstar-nfv-audit:${sha} -->`,
            }];
        assert.equal((await publish(args)).status, state === "duplicate" ? "duplicate" : "stale");
        assert.equal(commits.length + comments.length + outputs.length, 0);
    }
});

test("a head race fails explicitly without posting a success comment", async t => {
    const { args, comments } = fixture(t);
    args.github.graphql = async () => { throw new Error("expectedHeadOid does not match"); };
    await assert.rejects(publish(args), /expectedHeadOid/);
    assert.equal(comments.length, 0);
});

test("staged output cannot write to GitHub", async t => {
    const { args, commits, comments } = fixture(t);
    assert.equal((await publish({ ...args, staged: true })).status, "staged");
    assert.equal(commits.length + comments.length, 0);
});

test("payload validation rejects paths, duplicate files, mismatched SHAs, and false conclusive bundles", () => {
    for (const name of ["../Evil.fst", "/Evil.fst", ".github/workflows/Evil.fst", "Evil.fsti", "Evil\\Escape.fst"]) {
        assert.throws(() => validatePayload(payload({ files: [{ name, content: "bad" }] }), sha));
    }
    const file = { name: "PrAudit.fst", content: "module PrAudit" };
    assert.throws(() => validatePayload(payload({ files: [file, file] }), sha));
    assert.throws(() => validatePayload(payload({ files: [file, { ...file, name: "PRAudit.fst" }] }), sha));
    assert.throws(() => validatePayload(payload({ head_sha: "c".repeat(40) }), sha));
    assert.throws(() => validatePayload(payload({ files: [] }), sha));
    assert.throws(() => validatePayload(payload({ verdict: "safe" }), sha));
    assert.throws(() => validatePayload(payload({ files: [{ ...file, content: "x".repeat(65537) }] }), sha));
    assert.throws(() => validatePayload("x".repeat(256 * 1024 + 1), sha));
    assert.equal(validatePayload(payload({ verdict: "inconclusive", files: [] }), sha).verdict, "inconclusive");
});
