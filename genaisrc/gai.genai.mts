script({
    tools: ["agent_fs", "agent_git", "agent_github"],
    parameters: {
        workflow: { type: "string" }, // Workflow name
        failure_run_id: { type: "number" }, // ID of the failed run
        branch: { type: "string" }, // Branch name
    },
    model: "azure:gpt-4o",
    maxTokens: 2000
})

const {
    workflow = "cross-build.yml",
    failure_run_id = "11299772255",
    branch = await git.branch(),
} = env.vars

$`Investigate the status of the ${workflow} workflow and identify the root cause of the failure of run ${failure_run_id} in branch ${branch}.

- Correlate the failure with the latest commit.
- Do only consider the branch ${branch} in the analysis.
- Compare the source code between the failed run commit and the last successful run commit before that run.

In your report, include html links to the relevant runs, commits, pull requests or issues.
`
