script({
    tools: ["agent_fs", "agent_git", "agent_github"],
    model: "azure:gpt-4o",
    maxTokens: 20000
})

const {
    workflow = "RISC V and PowerPC 64",
    failure_run_id = "11296730058",
    branch = await git.defaultBranch(),
} = env.vars

$`Investigate the status of the ${workflow} workflow and identify the root cause of the failure of run ${failure_run_id} in branch ${branch}.

- Correlate the failure with the relevant commits, pull requests or issues.
- Compare the source code between the failed run commit and the last successful run commit before that run.

In your report, include html links to the relevant runs, commits, pull requests or issues.
`
