script({
    title: "Quantifier Instantiation Callbacks Podcast Generator",
    description: "Generate an engaging podcast script about Z3's quantifier instantiation callback feature",
    systemSafety: true,
    parameters: {
        style: {
            type: "string",
            description: "Podcast style: conversational, technical, or educational",
            default: "conversational"
        },
        duration: {
            type: "string", 
            description: "Target duration: short (5-10 min), medium (15-20 min), or long (25-30 min)",
            default: "medium"
        }
    },
})

const { style, duration } = env.vars

// Read the documentation and examples
const documentation = def("DOCUMENTATION", 
    await workspace.readText("doc/quantifier_instantiation_callback.md"), {
    language: "markdown",
    maxTokens: 8000
})

const pythonExample = def("PYTHON_EXAMPLE",
    await workspace.readText("examples/python/quantifier_instantiation_callback.py"), {
    language: "python", 
    maxTokens: 4000
})

const cppExample = def("CPP_EXAMPLE",
    await workspace.readText("examples/c++/quantifier_instantiation_callback.cpp"), {
    language: "cpp",
    maxTokens: 4000
})

const usageGuide = def("USAGE_GUIDE",
    await workspace.readText("examples/README_quantifier_callbacks.md"), {
    language: "markdown",
    maxTokens: 3000
})

$`## Task

You are a podcast script writer creating an engaging and informative podcast episode about Z3's quantifier instantiation callback feature. This is an advanced feature added in Z3 version 4.15.3 that allows fine-grained control over the theorem prover's quantifier instantiation process.

## Context

Based on the provided documentation (${documentation}), Python examples (${pythonExample}), C++ examples (${cppExample}), and usage guide (${usageGuide}), create a podcast script that makes this advanced feature accessible and interesting.

## Podcast Format

Style: ${style}
Target Duration: ${duration}

## Instructions

Create a ${style} podcast script with the following structure:

### Introduction (2-3 minutes)
- Hook: Start with an interesting problem that quantifier instantiation callbacks solve
- Brief introduction to Z3 and quantifiers
- What this episode will cover

### Main Content
- **What are quantifier instantiation callbacks?**
  - Explain in accessible terms what quantifiers are in Z3
  - How Z3 normally handles quantifier instantiation
  - What the callback feature adds

- **Why do we need this feature?**
  - Performance optimization scenarios
  - Custom solving strategies
  - Debugging and analysis use cases
  - Real-world examples where this matters

- **How to use it in practice**
  - Walk through a simple Python example
  - Show the callback signature and return values
  - Demonstrate the control flow

- **Advanced use cases**
  - Pattern-based filtering
  - Instantiation limiting strategies
  - Integration with larger solving workflows

- **Implementation across languages**
  - Python API (most accessible)
  - C++ API (for performance)
  - C API (for low-level integration)

### Conclusion (1-2 minutes)
- Recap of key benefits
- When to consider using this feature
- Resources for learning more

## Tone and Style Guidelines

For **conversational** style:
- Use a friendly, approachable tone
- Include analogies and real-world comparisons
- Have natural dialogue flow
- Make complex concepts accessible

For **technical** style:
- Focus on precise terminology
- Include more code examples
- Discuss implementation details
- Target experienced developers

For **educational** style:
- Build concepts step by step
- Include learning checkpoints
- Provide clear explanations
- Suitable for academic or training contexts

## Speaker Format

Use this format for dialogue:
**[Speaker Name]:** [Content]

Suggest 2-3 speakers:
- **Host:** Main presenter who guides the conversation
- **Expert:** Z3 developer or advanced user who provides technical insights
- **Newcomer:** Someone learning about the feature (for conversational style) or **Developer:** Implementation-focused perspective (for technical style)

## Technical Accuracy

- Ensure all technical details match the documentation
- Use correct API signatures and examples
- Explain the relationship to Z3's overall architecture
- Be precise about version requirements (4.15.3+)

Generate a complete podcast script that would result in approximately ${duration === "short" ? "5-10" : duration === "medium" ? "15-20" : "25-30"} minutes of content when spoken.`
