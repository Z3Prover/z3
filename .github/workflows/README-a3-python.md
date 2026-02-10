# A3 Python Code Analysis - Automated Bug Detection

## Overview

A3 Python Code Analysis is an AI-powered GitHub Agentic Workflow that automatically analyzes Python code in the Z3 repository using the `a3-python` tool. It identifies potential bugs, code quality issues, and provides actionable recommendations for improvements.

## Features

- **Automated Analysis**: Runs a3-python tool on all Python files in the `src/` directory
- **Smart Classification**: Distinguishes between true positives (real issues) and false positives
- **Issue Creation**: Automatically creates GitHub issues when 2+ likely issues are detected
- **Comprehensive Reports**: Includes severity levels, file locations, and fix recommendations
- **Weekly Schedule**: Runs automatically every Sunday to catch issues early
- **Manual Trigger**: Can be triggered on-demand via workflow dispatch

## How to Use

### Scheduled Runs (Automatic)

The workflow runs automatically every Sunday at midnight UTC. No action required.

### Manual Trigger (Workflow Dispatch)

1. Go to **Actions** → **A3 Python Code Analysis** in the GitHub repository
2. Click **Run workflow**
3. Select the branch (usually `main`)
4. Click **Run workflow**

The workflow will:
1. Install the a3-python tool from PyPI
2. Run analysis on all Python files in `src/`
3. Save output to `a3-python-output.txt`
4. Classify findings as true positives or false positives
5. Create a GitHub issue if 2+ likely issues are found

## What Gets Analyzed

The workflow analyzes:
- All Python files (`.py`) in the `src/` directory
- Python code for bugs, security issues, and quality problems
- Import statements and dependencies
- Code patterns and potential issues

## Issue Creation Logic

An issue is created **only when**:
- ✅ Analysis finds **2 or more true positives** (likely issues)
- ✅ Issues are actionable and specific
- ✅ Analysis completed successfully

An issue is **not created** when:
- ❌ Zero or one true positive found
- ❌ Only false positives detected
- ❌ Analysis failed to run
- ❌ No Python files found

## Issue Structure

When issues are created, they include:

### Summary Section
- Analysis date
- Total findings count
- True positives count
- False positives count

### True Positives Section
For each likely issue:
- **File**: Path to the affected file
- **Line**: Line number (if available)
- **Severity**: High / Medium / Low
- **Description**: Detailed explanation
- **Recommendation**: How to fix it

### Analysis Details
- False positives with dismissal reasons (collapsible)
- Complete raw output from a3-python (collapsible)

### Recommendations
- Prioritization guidance
- Action items

## Classification Criteria

### True Positives (Real Issues)
Issues that meet these criteria:
- Represents a real bug or problem
- Could impact functionality, security, or performance
- Actionable with a clear fix
- In code owned by the repository (not third-party)

Examples:
- Logic errors or bugs
- Security vulnerabilities
- Performance issues
- Broken imports or dependencies
- Type mismatches or incorrect usage

### False Positives (Not Issues)
Findings that are dismissed:
- Style preferences without functional impact
- Intentional design decisions
- Test code patterns
- Generated or vendored code
- Overly pedantic warnings

## Output Files

The workflow generates:
- `a3-python-output.txt`: Raw output from the a3-python analysis tool
  - Contains all findings from the tool
  - Includes errors, warnings, and recommendations
  - Saved in the workflow run artifacts

## Configuration

The workflow is configured with:

- **Trigger**: Weekly schedule (Sundays at midnight UTC) + manual dispatch
- **Timeout**: 45 minutes
- **Permissions**: Read-only (safe-outputs handle issue creation)
- **Labels**: Issues are labeled with `bug`, `automated-analysis`, `a3-python`
- **Tracker ID**: All issues include `a3-python-analysis` identifier for tracking

## Running a3-python Locally

To test the analysis locally:

```bash
# Install a3-python
pip install a3-python

# Run analysis on src directory
a3 analyze ./src

# Or with additional options
a3 analyze ./src --generate-docs --dependency-graph

# Or debug mode
a3 debug ./src --execute-tests --validate-imports
```

## Interpreting Results

When reviewing issues created by this workflow:

1. **Check Severity**: Start with high-severity issues first
2. **Verify the Issue**: Confirm it's a real problem in the codebase
3. **Review Recommendation**: Follow the suggested fix if appropriate
4. **Test Changes**: Ensure fixes don't break functionality
5. **Close or Comment**: Update the issue with your findings

## Customization

To modify the agent behavior without recompiling:

1. Edit `.github/workflows/a3-python.md` (the markdown body after `---`)
2. Changes take effect immediately on the next run
3. No compilation needed for prompt changes

For configuration changes (schedule, permissions, etc.):

```bash
# Edit the YAML frontmatter in .github/workflows/a3-python.md
# Then recompile:
gh aw compile a3-python
```

## Limitations

- Analyzes only Python files (`.py`) in the `src/` directory
- Depends on a3-python tool's capabilities and accuracy
- May have false positives that require human review
- Cannot automatically fix issues (only reports them)
- Requires API key if a3-python needs one (set `A3_API_KEY` secret)

## Security

- **Read-only permissions** for repository access
- **Safe outputs** handle all write operations (issue creation)
- **No secrets exposed** to the AI agent
- **Strict mode enabled** for enhanced security validation
- **Network access** controlled and limited

## Troubleshooting

### Tool Installation Fails
If a3-python fails to install, the workflow will report the error and exit gracefully.

### No Output Generated
If the analysis produces no output, the workflow will document this and exit without creating an issue.

### All False Positives
If all findings are false positives, the workflow will exit gracefully without creating an issue.

## Support

If the workflow encounters issues:
- Check the workflow run logs in the Actions tab
- Review error messages in the output
- Ensure Python files exist in the `src/` directory
- Verify a3-python tool is working: `pip install a3-python && a3 --version`

## See Also

- [a3-python on PyPI](https://pypi.org/project/a3/)
- [GitHub Agentic Workflows Documentation](https://github.github.com/gh-aw/)
- [Z3 Repository Structure](../../README.md)
