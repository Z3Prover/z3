# SpecBot: Automatic Specification Mining Agent

SpecBot is a GitHub Agentic Workflow that automatically annotates Z3 source code with formal specifications using LLM-based invariant synthesis.

## Overview

SpecBot analyzes C++ classes in the Z3 theorem prover codebase and automatically adds:
- **Class Invariants**: Properties that must always hold for all instances of a class
- **Pre-conditions**: Conditions required before a function executes
- **Post-conditions**: Guarantees about function results and side effects

This approach is inspired by the paper ["Classinvgen: Class invariant synthesis using large language models"](https://arxiv.org/abs/2502.18917).

## What It Does

### Automatic Specification Mining

SpecBot uses LLM reasoning to:
1. **Identify target classes** with complex state management
2. **Analyze code structure** including members, methods, and dependencies
3. **Mine specifications** using multi-step reasoning about code semantics
4. **Generate annotations** using Z3's existing assertion macros (`SASSERT`, `ENSURE`, `VERIFY`)
5. **Create pull requests** with the annotated code for human review

### Example Annotations

**Class Invariant:**
```cpp
class vector {
private:
    void check_invariant() const {
        SASSERT(m_size <= m_capacity);
        SASSERT(m_data != nullptr || m_capacity == 0);
    }
public:
    void push_back(int x) {
        check_invariant();  // Verify invariant
        // ... implementation
        check_invariant();  // Preserve invariant
    }
};
```

**Pre-condition:**
```cpp
void set_value(int index, int value) {
    SASSERT(index >= 0);           // Pre-condition
    SASSERT(index < m_size);       // Pre-condition
    // ... implementation
}
```

**Post-condition:**
```cpp
int* allocate_buffer(size_t size) {
    SASSERT(size > 0);              // Pre-condition
    int* result = new int[size];
    SASSERT(result != nullptr);     // Post-condition
    return result;
}
```

## Triggers

### 1. Weekly Schedule
- Automatically runs every week
- Randomly selects 3-5 core classes for analysis
- Focuses on high-impact components (AST, solvers, data structures)

### 2. Manual Trigger (workflow_dispatch)
You can manually trigger SpecBot with optional parameters:
- **target_path**: Specific directory or file (e.g., `src/ast/`, `src/smt/smt_context.cpp`)
- **target_class**: Specific class name to analyze

To trigger manually:
```bash
# Analyze a specific directory
gh workflow run specbot.lock.yml -f target_path=src/ast/

# Analyze a specific file
gh workflow run specbot.lock.yml -f target_path=src/smt/smt_context.cpp

# Analyze a specific class
gh workflow run specbot.lock.yml -f target_class=ast_manager
```

## Configuration

### Workflow Files
- **`.github/workflows/specbot.md`**: Workflow definition (compile this to update)
- **`.github/agentics/specbot.md`**: Agent prompt (edit without recompilation!)
- **`.github/workflows/specbot.lock.yml`**: Compiled workflow (auto-generated)

### Key Settings
- **Schedule**: Weekly (fuzzy scheduling to distribute load)
- **Timeout**: 45 minutes
- **Permissions**: Read-only (contents, issues, pull-requests)
- **Tools**: GitHub API, bash, file operations (view, glob, grep, edit)
- **Safe Outputs**: Creates pull requests, reports missing tools as issues

## Methodology

SpecBot follows a systematic approach to specification mining:

### 1. Class Selection
- Prioritizes classes with multiple data members and complex state
- Focuses on public/protected methods needing contracts
- Skips simple POD structs and well-annotated code

### 2. Code Analysis
- Parses header (.h) and implementation (.cpp) files
- Maps member variables, methods, and constructors
- Identifies resource management patterns

### 3. Specification Synthesis
Uses LLM reasoning to infer:
- **Invariants**: From member relationships, constructors, and state-modifying methods
- **Pre-conditions**: From argument constraints and defensive code patterns
- **Post-conditions**: From return value properties and guaranteed side effects

### 4. Annotation Generation
- Uses Z3's existing assertion macros
- Adds explanatory comments for complex invariants
- Follows Z3's coding conventions
- Guards expensive checks with `DEBUG` macros

### 5. Pull Request Creation
Creates a PR with:
- Detailed description of specifications added
- Rationale for each assertion
- Human review recommendations

## Best Practices

### What SpecBot Does Well ✅
- Identifies non-trivial invariants (not just null checks)
- Respects Z3's coding conventions
- Uses existing helper methods (e.g., `well_formed()`, `is_valid()`)
- Groups related assertions logically
- Considers performance impact

### What SpecBot Avoids ❌
- Trivial assertions that add no value
- Assertions with side effects
- Expensive checks without DEBUG guards
- Duplicating existing assertions
- Changing any program behavior

## Human Review Required

SpecBot is a **specification synthesis assistant**, not a replacement for human expertise:
- **Review all assertions** for correctness
- **Validate complex invariants** against code semantics
- **Check performance impact** of assertion checks
- **Refine specifications** based on domain knowledge
- **Test changes** before merging

LLMs can occasionally hallucinate or miss nuances, so human oversight is essential.

## Output Format

### Pull Request Structure
```markdown
## ✨ Automatic Specification Mining

### 📋 Classes Annotated
- `ClassName` in `src/path/to/file.cpp`

### 🔍 Specifications Added

#### Class Invariants
- **Invariant**: [description]
  - **Assertion**: `SASSERT([expression])`
  - **Rationale**: [why this invariant is important]

#### Pre-conditions
- **Method**: `method_name()`
  - **Pre-condition**: [description]
  - **Assertion**: `SASSERT([expression])`

#### Post-conditions
- **Method**: `method_name()`
  - **Post-condition**: [description]
  - **Assertion**: `SASSERT([expression])`

### 🎯 Goals Achieved
- ✅ Improved code documentation
- ✅ Early bug detection through runtime checks
- ✅ Better understanding of class contracts

*🤖 Generated by SpecBot - Automatic Specification Mining Agent*
```

## Editing the Agent

### Without Recompilation (Recommended)
Edit `.github/agentics/specbot.md` to modify:
- Agent instructions and guidelines
- Specification synthesis strategies
- Output formatting
- Error handling behavior

Changes take effect immediately on the next run.

### With Recompilation (For Config Changes)
Edit `.github/workflows/specbot.md` and run:
```bash
gh aw compile specbot
```

Recompilation is needed for:
- Changing triggers (schedule, workflow_dispatch)
- Modifying permissions or tools
- Adjusting timeout or safe outputs

## Troubleshooting

### Workflow Not Running
- Check that the compiled `.lock.yml` file is committed
- Verify the workflow is enabled in repository settings
- Review GitHub Actions logs for errors

### No Specifications Generated
- The selected classes may already be well-annotated
- Code may be too complex for confident specification synthesis
- Check workflow logs for analysis details

### Compilation Errors
If assertions cause build errors:
- Review assertion syntax and Z3 macro usage
- Verify that assertions don't access invalid members
- Check that expressions are well-formed

## Benefits

### For Developers
- **Documentation**: Specifications serve as precise documentation
- **Bug Detection**: Runtime assertions catch violations early
- **Understanding**: Clear contracts improve code comprehension
- **Maintenance**: Invariants help prevent bugs during refactoring

### For Verification
- **Foundation**: Specifications enable formal verification
- **Testing**: Assertions strengthen test coverage
- **Debugging**: Contract violations pinpoint error locations
- **Confidence**: Specifications increase correctness confidence

## References

- **Paper**: [Classinvgen: Class invariant synthesis using large language models (arXiv:2502.18917)](https://arxiv.org/abs/2502.18917)
- **Approach**: LLM-based specification mining for object-oriented code
- **Related**: Design by Contract, Programming by Contract (Bertrand Meyer)

## Contributing

To improve SpecBot:
1. Edit `.github/agentics/specbot.md` for prompt improvements
2. Provide feedback on generated specifications via PR reviews
3. Report issues or suggest enhancements through GitHub issues

## License

SpecBot is part of the Z3 theorem prover project and follows the same license (MIT).
