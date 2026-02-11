# A3 Python Workflow Fix

## Problem
The a3-python workflow was not finding Python files in the repository because it was using sparse-checkout and only checking out `.github` and `.agents` directories. The Python source files in `src/api/python/z3/` were not being checked out.

## Solution
Added a custom `steps:` configuration in the workflow frontmatter to run `git sparse-checkout add src` before the agent executes. This ensures the Python source files are available for analysis.

## Changes Made

### 1. Frontmatter Update (lines 24-28)
```yaml
steps:
  - name: Checkout Python source files
    run: |
      git sparse-checkout add src
      echo "Python source files checked out from src directory"
```

This step runs before the AI agent starts, expanding the sparse-checkout to include the `src/` directory.

### 2. Updated Analysis Instructions
- Updated Phase 2.1 to explicitly verify `src/api/python/z3/` files are available
- Changed the a3 command from `a3 analyze` to `a3 scan` with proper flags
- Added specific documentation about which Python files should be analyzed:
  - `z3.py` - Main Z3 Python API (350KB+)
  - `z3printer.py` - Pretty printing functionality
  - `z3num.py`, `z3poly.py`, `z3rcf.py` - Numeric and polynomial modules
  - `z3types.py`, `z3util.py` - Type definitions and utilities

### 3. Updated Exit Conditions
Added mention of sparse checkout issues in the exit conditions to help with future debugging.

## How to Recompile

After modifying `a3-python.md`, you must recompile the workflow to generate the updated `.lock.yml` file:

```bash
# Compile the specific workflow
gh aw compile a3-python

# Or compile all workflows
gh aw compile
```

This will update `a3-python.lock.yml` with the new sparse-checkout step.

## Testing

To test the workflow locally or in a PR:
1. Trigger the workflow manually via workflow_dispatch
2. Check the logs to verify:
   - The "Checkout Python source files" step runs successfully
   - Python files in `src/api/python/z3/` are found
   - The a3 scan command analyzes those files

## Related Files
- `a3-python.md` - The workflow definition (source of truth)
- `a3-python.lock.yml` - The compiled GitHub Actions workflow (auto-generated)
- `src/api/python/z3/*.py` - The Python files that should be analyzed
