# DeepTest - Automated Test Case Generator

## Overview

DeepTest is an AI-powered GitHub Agentic Workflow that automatically generates comprehensive test cases for Z3 source files. It analyzes a given source file and creates high-quality, production-ready tests covering basic functionality, edge cases, error handling, and integration scenarios.

## Features

- **Comprehensive Test Coverage**: Generates tests for basic functionality, edge cases, error handling, and integration scenarios
- **Multiple Languages**: Supports C++, Python, Java, C#, and other Z3 API languages
- **Smart Analysis**: Uses Serena language server for Python code analysis and grep/glob for C++ analysis
- **Automated PR Creation**: Creates a pull request with generated tests automatically
- **Follows Z3 Conventions**: Generates tests that match existing Z3 testing patterns and style
- **Persistent Memory**: Uses cache memory to track progress across runs

## How to Use

### Workflow Dispatch (Manual Trigger)

1. Go to **Actions** → **Deeptest** in the GitHub repository
2. Click **Run workflow**
3. Enter the file path (e.g., `src/util/vector.h`)
4. Optionally link to an issue number
5. Click **Run workflow**

The workflow will:
1. Analyze the source file
2. Generate comprehensive tests
3. Create a pull request with the test files
4. Optionally add a comment to the linked issue with statistics and instructions

## What Gets Generated

DeepTest creates test files that include:

### For C++ Files
- Unit tests using Z3's testing framework
- Located in `src/test/test_<module_name>.cpp`
- Follows existing test patterns in the repository
- Includes necessary headers and setup/teardown code

### For Python Files
- Unit tests using `unittest` or `pytest`
- Located in `src/api/python/test_<module_name>.py`
- Follows patterns from existing Python tests
- Includes proper imports and test fixtures

## Test Categories

Generated tests cover:

1. **Basic Functionality**: Happy path scenarios with typical inputs
2. **Edge Cases**: Boundary values, empty inputs, zero/negative values, very large inputs
3. **Error Handling**: Invalid parameters, null pointers, exceptions, assertion violations
4. **Integration Tests**: Realistic SMT-LIB2 formulas, solver workflows, theory combinations

## Output

After running, DeepTest will:

1. **Create a Pull Request** with:
   - Title: `[DeepTest] Add comprehensive tests for <filename>`
   - Generated test file(s)
   - Detailed description of test coverage
   - Instructions for running the tests
   - Labels: `automated-tests`, `deeptest`

2. **Post a Comment** with:
   - Test statistics (number of test cases by category)
   - Coverage percentage
   - Link to the created PR
   - Instructions for running the tests

## Example Usage

### Example 1: Test a C++ utility file
Via workflow dispatch with file path: `src/util/vector.h`

### Example 2: Test a Python API file
Via workflow dispatch with file path: `src/api/python/z3/z3.py`

### Example 3: Link to an issue
- File path: `src/ast/ast.cpp`
- Issue number: `1234` (optional)

## Running Generated Tests

After the PR is merged, run the tests:

```bash
# Build Z3
python scripts/mk_make.py
cd build && make -j$(nproc)

# Run the new tests
./test-z3 [test-name-pattern]
```

## Configuration

The workflow is configured with:

- **Timeout**: 30 minutes
- **Permissions**: Read-only (safe-outputs handle writes)
- **Network**: Default curated allow-list
- **Tools**: Serena (Python), bash, edit, grep, glob, GitHub API
- **Cache**: Persistent memory enabled

## Customization

To modify the agent behavior without recompiling:

1. Edit `.github/agentics/deeptest.md`
2. Changes take effect immediately (no compilation needed)
3. For configuration changes in `.github/workflows/deeptest.md`, run:
   ```bash
   gh aw compile deeptest
   ```

## Limitations

- Does not modify existing source files (only creates new test files)
- Focuses on public APIs and functions
- May not cover all internal implementation details
- Generated tests should be reviewed before merging

## Security

- **Read-only permissions** for the main job
- **Safe outputs** handle all write operations (PR creation, comments)
- **Network access** restricted to curated allow-list
- **No secrets exposed** to the AI agent

## Support

If DeepTest encounters issues or needs additional tools:
- It will automatically create an issue labeled `missing-tool`
- The issue will expire after 1 week if not addressed
- Check the workflow run logs for detailed error information

## See Also

- [GitHub Agentic Workflows Documentation](../.github/aw/github-agentic-workflows.md)
- [Z3 Testing Guide](../../README.md)
- [Z3 Build Instructions](../../README-CMake.md)
