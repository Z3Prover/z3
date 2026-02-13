---
on:
  schedule:
    - cron: "0 0 * * 0"  # Weekly on Sundays at midnight UTC
  workflow_dispatch:  # Allow manual trigger
permissions:
  contents: read
  issues: read
  pull-requests: read
network:
  allowed: [default, python]
tools:
  serena: ["python"]
safe-outputs:
  create-issue:
    labels:
      - bug
      - automated-analysis
      - a3-python
    title-prefix: "[a3-python] "
description: Analyzes Python code using a3-python tool to identify bugs and issues
name: A3 Python Code Analysis
strict: true
timeout-minutes: 45
tracker-id: a3-python-analysis
steps:
  - name: Checkout Python source files
    run: |
      git sparse-checkout init --cone
      git sparse-checkout set src
      echo "Source files checked out for Python analysis"
source: z3prover/z3/a3/a3-python-v2.md@a91c5c58bd975f336bf5b744885ffd4b36b2d2ec
---

# A3 Python Code Analysis Agent

You are an expert Python code analyst using the a3-python tool to identify bugs and code quality issues. Your mission is to analyze the Python codebase, identify true positives from the analysis output, and create GitHub issues when multiple likely issues are found.

## Current Context

- **Repository**: ${{ github.repository }}
- **Analysis Date**: $(date +%Y-%m-%d)
- **Workspace**: ${{ github.workspace }}

## Phase 1: Install and Setup a3-python

### 1.1 Install a3-python

Install the a3-python tool from PyPI:

```bash
pip install a3-python
```

Verify installation:

```bash
a3 --version || python -m a3 --version || echo "a3 command not found in PATH"
```

### 1.2 Check Available Commands

```bash
a3 --help || python -m a3 --help
```

## Phase 2: Run Analysis on Python Source Files

### 2.1 Identify Python Files

Find and verify Python source files in the repository:

```bash
# Check common source directories 
find ${{ github.workspace }} -name "*.py" -type f | grep -E "(src/|lib/|app/|project/)" | head -20

# List all Python files in the repository
find ${{ github.workspace }} -name "*.py" -type f | head -30
```

### 2.2 Run a3-python Analysis

Run the a3 scan command on the repository to analyze all Python files:

```bash
cd ${{ github.workspace }}

# Ensure PATH includes a3 command
export PATH="$PATH:/home/runner/.local/bin"

# Run a3 scan on the repository
if command -v a3 &> /dev/null; then
    # Run with multiple options for comprehensive analysis
    a3 scan . --verbose --dse-verify --deduplicate --consolidate-variants > a3-python-output.txt 2>&1 || \
    a3 scan . --verbose --functions --dse-verify > a3-python-output.txt 2>&1 || \
    a3 scan . --verbose > a3-python-output.txt 2>&1 || \
    echo "a3 scan command failed with all variations" > a3-python-output.txt
elif python -m a3 --help &> /dev/null; then
    python -m a3 scan . > a3-python-output.txt 2>&1 || \
    echo "python -m a3 scan command failed" > a3-python-output.txt
else
    echo "ERROR: a3-python tool not available" > a3-python-output.txt
fi

# Verify output was generated
ls -lh a3-python-output.txt
cat a3-python-output.txt
```

**Important**: The a3-python tool will analyze all Python files found in the repository, focusing on source code directories.

## Phase 3: Post-Process and Analyze Results

### 3.1 Review the Output

Read and analyze the contents of `a3-python-output.txt`:

```bash
cat a3-python-output.txt
```

### 3.2 Classify Findings

For each issue reported in the output, determine:

1. **True Positives (Likely Issues)**: Real bugs or code quality problems that should be addressed
   - Logic errors or bugs
   - Security vulnerabilities
   - Performance issues
   - Code quality problems
   - Broken imports or dependencies
   - Type mismatches or incorrect usage

2. **False Positives**: Findings that are not real issues
   - Style preferences without functional impact
   - Intentional design decisions
   - Test-related code patterns
   - Generated code or third-party code
   - Overly strict warnings without merit
   - **Assertion violations at the beginning of functions** (these are pre-conditions and intentional design)
   - Parameter validation checks in function entry points

### 3.3 Extract Source Code Context

For each true positive finding, extract the relevant source code context to make the report more readable:

```bash
# Function to extract source code context around a specific line
extract_code_context() {
    local file="$1"
    local line_num="$2"
    local context_lines="${3:-5}"  # Default to 5 lines before/after
    
    if [[ -f "$file" ]]; then
        echo "```python"
        # Show line numbers and context
        sed -n "$((line_num - context_lines)),$((line_num + context_lines))p" "$file" | \
        awk -v start=$((line_num - context_lines)) -v target=$line_num '{
            line_number = NR + start - 1
            if (line_number == target) {
                printf "%4d:❌ %s\n", line_number, $0
            } else {
                printf "%4d:   %s\n", line_number, $0
            }
        }'
        echo "```"
    else
        echo "File not found: $file"
    fi
}

# Export the function for use in subshells
export -f extract_code_context
```

For each true positive, collect the source code context:

```bash
# Example usage for each finding:
# extract_code_context "path/to/file.py" "line_number" 5

# Store contexts in a temporary file for later use in the issue
echo "# Source Code Contexts" > source_contexts.md
echo "" >> source_contexts.md

# For each true positive finding, extract context and append to file
# Example workflow:
for finding in "${true_positives[@]}"; do
    file=$(echo "$finding" | grep -o 'File: [^,]*' | cut -d' ' -f2)
    line=$(echo "$finding" | grep -o 'Line: [0-9]*' | cut -d' ' -f2)
    
    if [[ -n "$file" && -n "$line" ]]; then
        echo "## Finding in $file at line $line" >> source_contexts.md
        extract_code_context "$file" "$line" 5 >> source_contexts.md
        echo "" >> source_contexts.md
    fi
done
```

### 3.5 Enhanced Analysis Workflow

Create an enhanced analysis workflow that automatically extracts source code context. **IMPORTANT**: Limit detailed examples to top 5 high-severity findings only.

```bash
# Parse a3-python output and extract file/line information
parse_findings() {
    local output_file="$1"
    
    # Create arrays to store findings
    declare -a high_severity=()
    declare -a medium_severity=()
    declare -a false_positives=()
    
    # Parse the output file and extract findings with file/line info
    # This is a template - adjust parsing based on actual a3-python output format
    while IFS= read -r line; do
        if [[ "$line" =~ ^.*\.py:[0-9]+:.* ]]; then
            # Extract file and line number from the finding
            file=$(echo "$line" | grep -oP '[\w/.-]+\.py')
            line_num=$(echo "$line" | grep -oP '\.py:\K[0-9]+')
            description=$(echo "$line" | cut -d':' -f3-)
            
            echo "Found potential issue: $file:$line_num - $description"
            
            # Classify by severity and type
            # High severity: NULL_PTR, DIV_ZERO
            # Medium severity: BOUNDS, ASSERT_FAIL (except pre-condition assertions)
            # False positives: Assertion violations at function start (pre-conditions)
            
            if [[ "$description" =~ ASSERT_FAIL ]] && [[ $line_num -lt 10 ]]; then
                # Likely a pre-condition assertion at start of function
                false_positives+=("File: $file, Line: $line_num, Description: $description")
            elif [[ "$description" =~ (NULL_PTR|DIV_ZERO) ]]; then
                high_severity+=("File: $file, Line: $line_num, Description: $description")
            else
                medium_severity+=("File: $file, Line: $line_num, Description: $description")
            fi
        fi
    done < "$output_file"
    
    # Generate enhanced report with TOP 5 HIGH-SEVERITY findings only in detail
    echo "# Enhanced Analysis Report" > enhanced_report.md
    echo "" >> enhanced_report.md
    echo "## Sample High-Severity Findings (Top 5)" >> enhanced_report.md
    echo "" >> enhanced_report.md
    
    local counter=1
    local max_samples=5
    for finding in "${high_severity[@]}"; do
        if [ $counter -gt $max_samples ]; then
            break
        fi
        
        file=$(echo "$finding" | grep -o 'File: [^,]*' | cut -d' ' -f2)
        line_num=$(echo "$finding" | grep -o 'Line: [^,]*' | cut -d' ' -f2)
        desc=$(echo "$finding" | grep -o 'Description: .*' | cut -d' ' -f2-)
        
        echo "### $counter. $desc" >> enhanced_report.md
        echo "**Location**: \`$file:$line_num\`" >> enhanced_report.md
        echo "" >> enhanced_report.md
        
        if [[ -f "$file" ]]; then
            extract_code_context "$file" "$line_num" 5 >> enhanced_report.md
        else
            echo "```" >> enhanced_report.md
            echo "File not found: $file" >> enhanced_report.md
            echo "```" >> enhanced_report.md
        fi
        
        echo "" >> enhanced_report.md
        ((counter++))
    done
    
    # Add summary statistics
    echo "## Summary Statistics" >> enhanced_report.md
    echo "- High Severity: ${#high_severity[@]}" >> enhanced_report.md
    echo "- Medium Severity: ${#medium_severity[@]}" >> enhanced_report.md
    echo "- False Positives: ${#false_positives[@]}" >> enhanced_report.md
    
    # Display the enhanced report
    echo "=== Enhanced Analysis Report ==="
    cat enhanced_report.md
}

# Run the enhanced analysis
parse_findings "a3-python-output.txt"
```

**Note**: The complete list of all findings should be added to a collapsible `<details>` section in the GitHub issue, not shown in full detail.

### 3.4 Categorize and Count

Create a structured analysis with source code context:

```markdown
## Analysis Results

### 3.4 Categorize and Count

Create a structured analysis with source code context:

```markdown
## Analysis Results

### High-Severity Issues (for detailed examples):
1. [Issue 1 Description] - File: path/to/file.py, Line: X
   **Source Code Context:**
   ```python
   [Line numbers with context - error line marked with ❌]
   ```

2. [Issue 2 Description] - File: path/to/file.py, Line: Y
   **Source Code Context:**
   ```python
   [Line numbers with context - error line marked with ❌]
   ```

(Limit to top 5 high-severity for detailed display)

### False Positives:
1. [FP 1 Description] - Reason: Pre-condition assertion at function start
2. [FP 2 Description] - Reason for dismissal
...

### Summary:
- Total findings: X
- High severity (NULL_PTR, DIV_ZERO): Y
- Medium severity (BOUNDS, ASSERT_FAIL): Z
- False positives (including pre-conditions): W
```

## Phase 4: Create GitHub Issue (Conditional)

### 4.1 Determine If Issue Creation Is Needed

Create a GitHub issue **ONLY IF**:
- ✅ There are **2 or more** true positives (likely issues)
- ✅ The issues are actionable and specific
- ✅ The analysis completed successfully

**Do NOT create an issue if**:
- ❌ Zero or one true positive found
- ❌ Only false positives detected
- ❌ Analysis failed to run
- ❌ Output file is empty or contains only errors

### 4.2 Generate Issue Description

**Important**: Use the enhanced report generated in Phase 3.5 to populate the issue with source code context.

If creating an issue, use this structure:

```markdown
## A3 Python Code Analysis - [Date]

This issue reports **[number]** DSE-confirmed bugs identified by a3-python analysis tool across the Z3 Python API.

### Executive Summary

- **Total Findings**: X confirmed bugs
- **High Severity**: Y (NULL_PTR: N1, DIV_ZERO: N2)
- **Medium Severity**: Z (BOUNDS: N3, ASSERT_FAIL: N4)
- **Analysis Method**: Deep Symbolic Execution (DSE) verification

### Files Most Affected

| File | Issues |
|------|--------|
| `path/to/file1.py` | X |
| `path/to/file2.py` | Y |
| `path/to/file3.py` | Z |

(Show only top 3-5 files)

### Sample High-Severity Findings

#### 1. [BUG_TYPE] in `function_name`

**Location**: `path/to/file.py:line_number`

```python
  10:   def some_function():
  11:       value = None
  12: ❌     return value.upper()  # Error: NoneType has no attribute 'upper'
  13:   
  14:   # Rest of function...
```

#### 2. [BUG_TYPE] in `function_name`

**Location**: `path/to/file.py:line_number`

```python
  25:   if condition:
  26:       result = process_data()
  27: ❌     return result  # Error: 'result' may be undefined
  28:   # Missing else clause
```

(Show only top 5 high-severity examples with code context)

### Bug Type Analysis

| Type | Count | Description |
|------|-------|-------------|
| NULL_PTR | X | Potential None/null dereferences |
| BOUNDS | Y | Array/string index out of bounds |
| ASSERT_FAIL | Z | Assertion violations |
| DIV_ZERO | W | Division by zero errors |

### Methodology

This analysis used **a3-python** with:
- ✅ **Deep Symbolic Execution (DSE)**: Confirms bug reachability via concrete paths
- ✅ **Barrier Theory**: Attempts to prove safety before flagging
- ✅ **Multi-strategy verification**: 7+ verification techniques

All [number] issues are **DSE-confirmed**, meaning the tool verified these errors are reachable through real execution paths.

### Recommended Actions

**Immediate Priority** (High Severity - X issues):
1. Add null/None checks before dereferences in core API functions
2. Validate division denominators to prevent DIV_ZERO
3. Focus on `most_affected_file.py` (N issues)

**Medium Priority** (Y issues):
1. Add bounds checking for array/string indexing
2. Review and strengthen assertion conditions
3. Add comprehensive error handling

**Long-term**:
1. Adopt comprehensive input validation across Python API
2. Use Python type hints consistently (e.g., `Optional[T]`)
3. Consider defensive programming patterns for C API wrappers

### Complete Analysis Data

<details>
<summary>All [number] findings grouped by file (click to expand)</summary>

**path/to/file1.py** (X issues)
- BUG_TYPE: N issues
  - Line Y: `function_name`
  - Line Z: `function_name`
  ...

**path/to/file2.py** (X issues)
- BUG_TYPE: N issues
  - Line Y: `function_name`
  ...

(List ALL findings in collapsed section)

</details>

<details>
<summary>Raw a3-python output excerpt (click to expand)</summary>

```
[PASTE FIRST 50-100 LINES OF a3-python-output.txt HERE FOR REFERENCE]
```

</details>

---

*Note: All findings have been DSE-confirmed by a3-python's deep symbolic execution engine. For questions about specific findings, run `a3 scan` locally for detailed analysis.*
```

### 4.3 Use Safe Outputs

Create the issue using the safe-outputs configuration:

- Title will be prefixed with `[a3-python]`
- Labeled with `bug`, `automated-analysis`, `a3-python`
- Contains structured analysis with actionable findings

## Important Guidelines

### Analysis Quality
- **Be thorough**: Review all findings carefully
- **Be accurate**: Distinguish real issues from false positives
- **Be specific**: Provide file names, line numbers, and descriptions
- **Be actionable**: Include recommendations for fixes
- **Be concise**: Focus on the most critical findings in the main issue body

### Issue Formatting Best Practices
- **Limit sample findings**: Show only top 5 high-severity examples with code context
- **Use collapsible sections**: Put complete analysis data in `<details>` tags
- **Prioritize readability**: Organize by severity and actionability, not just by file
- **Avoid duplication**: Don't repeat the same information in multiple formats
- **Keep it focused**: The issue should be scannable in under 2 minutes

### Classification Criteria

**True Positives** should meet these criteria:
- The issue represents a real bug or problem
- It could impact functionality, security, or performance
- It's actionable with a clear fix
- It's in code owned by the repository (not third-party)

**False Positives** typically include:
- Style preferences without functional impact
- Intentional design decisions that are correct
- Test code patterns that look unusual but are valid
- Generated or vendored code
- Overly pedantic warnings
- **Assertion violations at the beginning of functions** (these are pre-conditions)
- Parameter validation checks (assert statements checking input parameters)

### Threshold for Issue Creation
- **2+ true positives**: Create an issue with all findings
- **1 true positive**: Do not create an issue (not enough to warrant it)
- **0 true positives**: Exit gracefully without creating an issue

### Exit Conditions

Exit gracefully without creating an issue if:
- Analysis tool failed to run or install
- Python source files were not found or checked out properly
- No Python files found in repository
- Output file is empty or invalid
- Zero or one true positive identified
- All findings are false positives

### Success Metrics

A successful analysis:
- ✅ Completes without errors
- ✅ Generates comprehensive output with source code context
- ✅ Accurately classifies findings
- ✅ Creates actionable issue when appropriate
- ✅ Provides clear recommendations with visual code examples
- ✅ Shows error lines with surrounding context for better understanding

## Output Requirements

Your output MUST either:

1. **If analysis fails or no findings**:
   ```
   ✅ A3 Python analysis completed.
   No significant issues found - 0 or 1 true positive detected.
   ```

2. **If 2+ true positives found**: Create an issue with:
   - Clear executive summary with statistics
   - Files most affected table (top 3-5 only)
   - **ONLY top 5 high-severity findings** with detailed source code context
   - Bug type analysis summary table
   - Methodology explanation
   - Recommended actions (prioritized)
   - **Complete findings list** in collapsed `<details>` section
   - **Raw output excerpt** (first 50-100 lines) in collapsed `<details>` section
   
**Critical**: Do NOT list all findings in the main issue body. Keep sample findings to 5 maximum and put comprehensive data in collapsible sections.

## Enhanced Workflow Summary

The enhanced workflow now includes:

1. **Automated Source Code Context Extraction**: The `extract_code_context` function automatically extracts 5 lines before and after each error location
2. **Visual Error Highlighting**: Error lines are marked with ❌ for easy identification
3. **Severity-Based Classification**: Automatically categorizes findings as high/medium severity
4. **False Positive Detection**: Identifies pre-condition assertions at function entry points
5. **Concise Reporting**: Limits detailed examples to top 5 high-severity findings
6. **Progressive Disclosure**: Uses collapsible sections for complete data
7. **Enhanced GitHub Issues**: Issues are scannable, actionable, and well-organized

Begin the analysis now. Install a3-python, run analysis on the repository, save output to a3-python-output.txt, extract source code context for findings, classify by severity, and create a GitHub issue if 2 or more likely issues are found. **Remember to keep the main issue body concise with only top 5 examples and put complete findings in a collapsed section.**
