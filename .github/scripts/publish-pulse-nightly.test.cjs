const assert = require("node:assert/strict");
const crypto = require("node:crypto");
const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const test = require("node:test");
const { publish } = require("./publish-pulse-nightly.cjs");

const sha = "a".repeat(40);

function fixture(t) {
    const artifactDir = fs.mkdtempSync(path.join(os.tmpdir(), "pulse-nightly-test-"));
    t.after(() => fs.rmSync(artifactDir, { recursive: true }));
    for (const backend of ["ocaml", "cherry"]) {
        const directory = path.join(artifactDir, backend);
        fs.mkdirSync(directory);
        const name = `pulse-checker-${backend}-linux-x86_64.tar.gz`;
        const data = Buffer.from(`${backend} checker package`);
        fs.writeFileSync(path.join(directory, name), data);
        const digest = crypto.createHash("sha256").update(data).digest("hex");
        fs.writeFileSync(path.join(directory, `${name}.sha256`), `${digest}  ${name}\n`);
    }
    const mutations = [], notices = [];
    const context = {
        repo: { owner: "Z3Prover", repo: "z3" },
        payload: {
            repository: { default_branch: "master" },
            workflow_run: {
                conclusion: "success", path: ".github/workflows/nightly.yml",
                head_repository: { full_name: "Z3Prover/z3" },
                head_branch: "master", event: "schedule", head_sha: sha,
            },
        },
    };
    const ref = { object: { type: "commit", sha } };
    const assets = [{ id: 1, name: "z3-linux.zip" }];
    const args = {
        context, artifactDir,
        core: {
            notice: message => notices.push(message),
            summary: { addLink() { return this; }, addRaw() { return this; }, async write() {} },
        },
        github: {
            rest: {
                git: { getRef: async () => ({ data: ref }) },
                repos: {
                    getReleaseByTag: async () => ({ data: {
                        id: 123, html_url: "https://github.com/Z3Prover/z3/releases/tag/Nightly",
                    } }),
                    listReleaseAssets() {},
                    deleteReleaseAsset: async item => mutations.push({ delete: item }),
                    uploadReleaseAsset: async item => mutations.push({ upload: item }),
                },
            },
            paginate: async () => assets,
        },
    };
    return { args, mutations, notices, ref, assets };
}

test("nightly publication adds both checker packages and checksums to the checked release", async t => {
    const { args, mutations } = fixture(t);
    assert.equal((await publish(args)).status, "published");
    assert.equal(mutations.length, 4);
    for (const { upload } of mutations) {
        assert.equal(upload.release_id, 123);
        assert.match(upload.name, /^pulse-checker-(ocaml|cherry)-linux-x86_64\.tar\.gz(\.sha256)?$/);
        assert.equal(upload.data.length, upload.headers["content-length"]);
    }
});

test("reruns replace only the four checker assets, leaving solver packages untouched", async t => {
    const { args, mutations, assets } = fixture(t);
    assets.push({ id: 2, name: "pulse-checker-ocaml-linux-x86_64.tar.gz" });
    await publish(args);
    assert.deepEqual(mutations.filter(item => item.delete).map(item => item.delete.asset_id), [2]);
});

test("an older nightly cannot publish into a newer release", async t => {
    const { args, mutations, notices, ref } = fixture(t);
    ref.object.sha = "b".repeat(40);
    assert.equal((await publish(args)).status, "stale");
    assert.equal(mutations.length, 0);
    assert.equal(notices.length, 1);
});

test("non-nightly, failed, fork, and non-default branch runs cannot publish", async t => {
    for (const changes of [
        { conclusion: "failure" }, { path: ".github/workflows/ci.yml" },
        { head_repository: { full_name: "other/z3" } }, { head_branch: "feature" },
        { event: "pull_request" }, { head_sha: "bad" },
    ]) {
        const { args, mutations } = fixture(t);
        Object.assign(args.context.payload.workflow_run, changes);
        await assert.rejects(publish(args), /successful default-branch nightly/);
        assert.equal(mutations.length, 0);
    }
});

test("corrupt or missing packages fail before changing release assets", async t => {
    for (const missing of [false, true]) {
        const { args, mutations } = fixture(t);
        const filename = path.join(args.artifactDir, "cherry", "pulse-checker-cherry-linux-x86_64.tar.gz");
        if (missing) fs.unlinkSync(filename);
        else fs.appendFileSync(filename, "corruption");
        await assert.rejects(publish(args), missing ? /ENOENT/ : /Checksum mismatch/);
        assert.equal(mutations.length, 0);
    }
});

test("release deletion during upload fails explicitly rather than publishing to a new release", async t => {
    const { args } = fixture(t);
    args.github.rest.repos.uploadReleaseAsset = async () => { throw new Error("Release not found"); };
    await assert.rejects(publish(args), /Release not found/);
});
