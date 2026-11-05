const crypto = require("node:crypto");
const fs = require("node:fs");
const path = require("node:path");

async function publish({ github, context, core, artifactDir }) {
    const run = context.payload.workflow_run;
    const repository = `${context.repo.owner}/${context.repo.repo}`.toLowerCase();
    if (!run || run.conclusion !== "success" ||
        run.path?.split("@")[0] !== ".github/workflows/nightly.yml" ||
        run.head_repository?.full_name.toLowerCase() !== repository ||
        run.head_branch !== context.payload.repository.default_branch ||
        !["schedule", "workflow_dispatch"].includes(run.event) ||
        !/^[0-9a-f]{40}$/.test(run.head_sha))
        throw new Error("Publication requires a successful default-branch nightly build");

    const files = [];
    for (const backend of ["ocaml", "cherry"]) {
        const name = `pulse-checker-${backend}-linux-x86_64.tar.gz`;
        const data = fs.readFileSync(path.join(artifactDir, backend, name));
        const checksum = fs.readFileSync(path.join(artifactDir, backend, `${name}.sha256`));
        const digest = crypto.createHash("sha256").update(data).digest("hex");
        if (checksum.toString("utf8").trim() !== `${digest}  ${name}`)
            throw new Error(`Checksum mismatch for ${name}`);
        files.push({ name, data, type: "application/gzip" });
        files.push({ name: `${name}.sha256`, data: checksum, type: "text/plain" });
    }

    const repo = context.repo;
    const { data: release } = await github.rest.repos.getReleaseByTag({
        ...repo, tag: "Nightly",
    });
    const { data: ref } = await github.rest.git.getRef({
        ...repo, ref: "tags/Nightly",
    });
    if (ref.object.type !== "commit" || ref.object.sha !== run.head_sha) {
        const message = "Skipping stale checker packages: Nightly no longer points to the triggering build.";
        core.notice(message);
        await core.summary.addRaw(message).write();
        return { status: "stale" };
    }
    const assets = await github.paginate(github.rest.repos.listReleaseAssets, {
        ...repo, release_id: release.id, per_page: 100,
    });
    for (const file of files) {
        const old = assets.find(asset => asset.name === file.name);
        if (old)
            await github.rest.repos.deleteReleaseAsset({ ...repo, asset_id: old.id });
        // Address the checked release ID, never a moving tag, when uploading.
        await github.rest.repos.uploadReleaseAsset({
            ...repo, release_id: release.id, name: file.name, data: file.data,
            headers: { "content-type": file.type, "content-length": file.data.length },
        });
    }
    await core.summary.addLink("Nightly checker packages", release.html_url)
        .addRaw(`\n\nBuilt from \`${run.head_sha}\`.\n`).write();
    return { status: "published" };
}

module.exports = { publish };
