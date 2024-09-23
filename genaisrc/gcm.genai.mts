/**
 * git commit flow with auto-generated commit message
 */
script({
    title: "git commit message",
    description: "Generate a commit message for all staged changes",
})

// TODO: update this diff command to match your workspace
const diffCmd = "git diff --cached -- . :!**/genaiscript.d.ts"

// Check for staged changes and stage all changes if none are staged
let diff = await host.exec(diffCmd)
if (!diff.stdout) {
    /**
     * Ask user to stage all changes if none are staged
     */
    const stage = await host.confirm("No staged changes. Stage all changes?", {
        default: true,
    })
    if (stage) {
        // Stage all changes and recompute diff
        await host.exec("git add .")
        diff = await host.exec(diffCmd)
    }
    if (!diff.stdout) cancel("no staged changes")
}

// show diff in the console
console.log(diff.stdout)

let choice
let message
do {
    // Generate commit message
    const res = await runPrompt(
        (_) => {
            _.def("GIT_DIFF", diff, { maxTokens: 20000 })
            _.$`GIT_DIFF is a diff of all staged changes, coming from the command:
\`\`\`
git diff --cached
\`\`\`
Please generate a concise, one-line commit message for these changes.
- do NOT add quotes
` // TODO: add a better prompt
        },
        { cache: false, temperature: 0.8 }
    )
    if (res.error) throw res.error

    message = res.text
    if (!message) {
        console.log("No message generated, did you configure the LLM model?")
        break
    }

    // Prompt user for commit message
    choice = await host.select(message, [
        {
            value: "commit",
            description: "accept message and commit",
        },
        {
            value: "edit",
            description: "edit message and commit",
        },
        {
            value: "regenerate",
            description: "regenerate message",
        },
    ])

    // Handle user choice
    if (choice === "edit") {
        message = await host.input("Edit commit message", {
            required: true,
        })
        choice = "commit"
    }
    // Regenerate message
    if (choice === "commit" && message) {
        console.log((await host.exec("git", ["commit", "-m", message])).stdout)
        if (await host.confirm("Push changes?", { default: true }))
            console.log((await host.exec("git push")).stdout)
        break
    }
} while (choice !== "commit")
