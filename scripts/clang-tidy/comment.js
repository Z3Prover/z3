// Copyright (c) 2026 Microsoft Corporation
// SPDX-License-Identifier: MIT
// Loaded from the default branch by the privileged workflow, never from a PR.
const fs = require('node:fs');
const MARKER = '<!-- z3-ast-argument-order -->';
const RUN_MARKER = /<!-- z3-ast-order-run:(\d+):(\d+) -->/;
const EDITED_MARKER = /^(<!-- z3-ast-argument-order -->\n)\*\*EDITED: \d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2} UTC\*\*\n\n/;
const SHA = /^[0-9a-f]{40}$/;
const count = n => Number.isSafeInteger(n) && n >= 0 && n <= 10000000;
const signed = n => n >= 0 ? `+${n}` : `${n}`;
const escape = s => s.replace(/[&<>@`|\\[\]*_]/g, c => `&#${c.charCodeAt(0)};`);
const relativePath = p => typeof p === 'string' && p.length > 0 && p.length <= 1024 &&
    !p.startsWith('/') && !p.split('/').includes('..') && !/[\x00-\x1f\x7f]/.test(p);

function readReport(file) {
    const stat = fs.lstatSync(file);
    if (!stat.isFile() || stat.size > 1024 * 1024) throw new Error('Invalid comparison artifact');
    const r = JSON.parse(fs.readFileSync(file, 'utf8'));
    if (r.schema_version !== 1 || !SHA.test(r.head_sha) || !SHA.test(r.tested_sha) || !count(r.head_count) ||
        !Array.isArray(r.files) || r.files.length > 10000 ||
        !(r.base_sha === null && r.base_count === null || SHA.test(r.base_sha) && count(r.base_count))) {
        throw new Error('Invalid comparison schema');
    }
    if (r.scope !== undefined) {
        const s = r.scope;
        if (!s || !['affected', 'full'].includes(s.mode) ||
            !count(s.head_units) || !count(s.head_total) || !s.head_total || s.head_units > s.head_total ||
            (r.base_count === null ? s.base_units !== null || s.base_total !== null :
                !count(s.base_units) || !count(s.base_total) || !s.base_total || s.base_units > s.base_total) ||
            s.mode === 'full' && (s.head_units !== s.head_total || s.base_units !== s.base_total) ||
            s.head_units === 0 && r.head_count !== 0 || s.base_units === 0 && r.base_count !== 0) {
            throw new Error('Invalid scan scope');
        }
    }
    const paths = new Set();
    for (const f of r.files) {
        if (!relativePath(f.path) ||
            paths.has(f.path) || !count(f.base) || !count(f.head) || f.base === f.head ||
            f.base > r.base_count || f.head > r.head_count) {
            throw new Error('Invalid per-file counts');
        }
        paths.add(f.path);
    }
    if (r.base_count === null && r.files.length) throw new Error('Unexpected baseline file counts');
    if (r.base_count !== null) {
        const base = r.files.reduce((n, f) => n + f.base, 0);
        const head = r.files.reduce((n, f) => n + f.head, 0);
        if (base > r.base_count || head > r.head_count || head - base !== r.head_count - r.base_count) {
            throw new Error('Inconsistent comparison totals');
        }
    }
    // Optional for artifacts produced by workflows already in flight.
    if (r.warning_diff !== undefined) {
        const diff = r.warning_diff, deltas = new Map();
        if (r.base_count === null || !diff || !Array.isArray(diff.removed) || !Array.isArray(diff.added) ||
            diff.removed.length > r.base_count || diff.added.length > r.head_count ||
            diff.removed.length + diff.added.length > 10000 ||
            diff.added.length - diff.removed.length !== r.head_count - r.base_count) {
            throw new Error('Invalid warning diff');
        }
        for (const [warnings, sign] of [[diff.removed, -1], [diff.added, 1]]) {
            const seen = new Set();
            for (const w of warnings) {
                if (!w || !relativePath(w.file) || !count(w.line) || !w.line || !count(w.column) || !w.column ||
                    typeof w.message !== 'string' || !w.message.length || w.message.length > 4096 ||
                    /[\x00-\x1f\x7f]/.test(w.message)) throw new Error('Invalid warning diagnostic');
                const key = JSON.stringify([w.file, w.line, w.column, w.message]);
                if (seen.has(key)) throw new Error('Duplicate warning diagnostic');
                seen.add(key);
                deltas.set(w.file, (deltas.get(w.file) || 0) + sign);
            }
        }
        for (const f of r.files) {
            if (deltas.get(f.path) !== f.head - f.base) throw new Error('Inconsistent warning diff');
            deltas.delete(f.path);
        }
        if ([...deltas.values()].some(n => n !== 0)) throw new Error('Inconsistent warning diff');
    }
    return r;
}

function render(r) {
    const lines = ['### AST argument-order warnings', ''];
    if (r.scope) {
        const s = r.scope;
        if (s.base_units === 0 && s.head_units === 0) lines.push('No C++ translation units are affected by this PR.', '');
        else {
            const sides = s.base_units === null ? `**${s.head_units}/${s.head_total}** translation units` :
                `base **${s.base_units}/${s.base_total}**, PR **${s.head_units}/${s.head_total}** translation units`;
            lines.push(`${s.mode === 'affected' ? 'Warnings in affected files' : 'Full scan'} (${sides}).`, '');
        }
    }
    if (r.base_count === null) lines.push(`Warnings: **${r.head_count}** (\`${r.head_sha.slice(0, 12)}\`).`);
    else {
        lines.push(`Base: **${r.base_count}** → PR: **${r.head_count}**; change: **${signed(r.head_count - r.base_count)}**.`, '',
                   `Base \`${r.base_sha.slice(0, 12)}\`; head \`${r.head_sha.slice(0, 12)}\`.`);
        if (r.tested_sha !== r.head_sha) lines.push(`Tested the PR merged into its base (\`${r.tested_sha.slice(0, 12)}\`).`);
        if (r.files.length) {
            lines.push('', '| File | Base | PR | Change |', '| --- | ---: | ---: | ---: |');
            for (const f of r.files.slice(0, 30)) {
                const label = f.path.length > 240 ? f.path.slice(0, 237) + '...' : f.path;
                lines.push(`| ${escape(label)} | ${f.base} | ${f.head} | ${signed(f.head - f.base)} |`);
            }
            if (r.files.length > 30) lines.push('', `Showing 30 of ${r.files.length} files with changed counts.`);
        }
        if (r.warning_diff) {
            const diff = [];
            let total = 0, length = 0;
            for (const [warnings, sign] of [[r.warning_diff.removed, '-'], [r.warning_diff.added, '+']]) {
                for (const w of warnings) {
                    ++total;
                    const line = `${sign} ${w.file}:${w.line}:${w.column}: warning: ${w.message} [z3-ast-argument-order]`;
                    if (diff.length < 100 && length + line.length + 1 <= 12000) {
                        diff.push(line);
                        length += line.length + 1;
                    }
                }
            }
            lines.push('', '<details>', '<summary>Warning diff</summary>', '');
            // Diagnostics are single lines prefixed with +/-; their contents
            // cannot close the code fence or inject Markdown/HTML outside it.
            if (total) lines.push('```diff', ...diff, '```');
            else lines.push('No warning changes.');
            if (diff.length < total) lines.push('', `Showing ${diff.length} of ${total} warning changes; full diagnostics are in the run artifacts.`);
            lines.push('', '</details>');
        }
    }
    return lines.join('\n');
}

async function post({github, context, core, reportPath}) {
    const run = context.payload.workflow_run;
    const {owner, repo} = context.repo;
    if (run.event !== 'pull_request' || !run.head_repository || run.repository.full_name !== `${owner}/${repo}` ||
        run.path.split('@')[0] !== '.github/workflows/ast-order-warning-report.yml' ||
        ['cancelled', 'skipped'].includes(run.conclusion)) return;

    // PR associations come from GitHub, never from the untrusted artifact.
    // Fork workflow_run payloads can have an empty pull_requests array.
    const candidates = run.pull_requests?.length ? run.pull_requests :
        await github.paginate(github.rest.pulls.list, {owner, repo, state: 'open', per_page: 100,
            head: `${run.head_repository.owner.login}:${run.head_branch}`});
    const report = run.conclusion === 'success' ? readReport(reportPath) : null;
    if (report && (report.head_sha !== run.head_sha || report.base_sha === null)) {
        throw new Error('Comparison does not match the triggering PR run');
    }
    for (const candidate of candidates) {
        const {data: pr} = await github.rest.pulls.get({owner, repo, pull_number: candidate.number});
        if (pr.state !== 'open' || pr.base.repo.full_name !== `${owner}/${repo}` ||
            pr.head.sha !== run.head_sha || pr.head.repo?.id !== run.head_repository.id ||
            report && pr.base.sha !== report.base_sha) {
            core.info(`Skipping stale or unrelated report for #${pr.number}`);
            continue;
        }
        const url = `${context.serverUrl}/${owner}/${repo}/actions/runs/${run.id}`;
        const text = report ? render(report) :
            '### AST argument-order warnings\n\nComparison unavailable: a build, scan, or report step failed. No warning delta is reported.';
        const body = `${MARKER}\n${text}\n\n[CI run and diagnostics](${url})\n<!-- z3-ast-order-run:${run.id}:${run.run_attempt} -->`;
        const comments = await github.paginate(github.rest.issues.listComments,
                                              {owner, repo, issue_number: pr.number, per_page: 100});
        const previous = comments.find(c => c.user?.login === 'github-actions[bot]' &&
                                           c.user.type === 'Bot' && c.body?.startsWith(MARKER));
        const oldRun = previous?.body.match(RUN_MARKER);
        if (oldRun && (Number(oldRun[1]) > run.id ||
                       Number(oldRun[1]) === run.id && Number(oldRun[2]) > run.run_attempt)) continue;
        if (previous) {
            // Ignore the previous edit date when deciding whether content changed.
            if (previous.body.replace(EDITED_MARKER, '$1') === body) continue;
            const date = new Date().toISOString().slice(0, 19).replace('T', ' ');
            const editedBody = body.replace(MARKER, `${MARKER}\n**EDITED: ${date} UTC**\n`);
            await github.rest.issues.updateComment({owner, repo, comment_id: previous.id, body: editedBody});
        }
        else await github.rest.issues.createComment({owner, repo, issue_number: pr.number, body});
    }
}

module.exports = {post};
if (require.main === module) console.log(render(readReport(process.argv[2])));
