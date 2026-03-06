#!/usr/bin/env python
# Copyright (c) Microsoft Corporation 2025
"""
Z3 Go API documentation generator script

This script generates HTML documentation for the Z3 Go bindings.
It creates a browsable HTML interface for the Go API documentation.
"""

import os
import sys
import subprocess
import argparse
import re

SCRIPT_DIR = os.path.abspath(os.path.dirname(__file__))
GO_API_PATH = os.path.join(SCRIPT_DIR, '..', 'src', 'api', 'go')
OUTPUT_DIR = os.path.join(SCRIPT_DIR, 'api', 'html', 'go')

def extract_types_and_functions(filepath):
    """Extract type and function names from a Go source file."""
    types = []
    functions = []
    
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
            
            # Extract type declarations
            type_pattern = r'type\s+(\w+)\s+(?:struct|interface)'
            types = re.findall(type_pattern, content)
            
            # Extract function/method declarations
            # Match both: func Name() and func (r *Type) Name()
            func_pattern = r'func\s+(?:\([^)]+\)\s+)?(\w+)\s*\('
            functions = re.findall(func_pattern, content)
            
    except Exception as e:
        print(f"Warning: Could not parse {filepath}: {e}")
    
    return types, functions

def extract_detailed_api(filepath):
    """Extract detailed type and function information with signatures and comments."""
    types_info = {}
    functions_info = []
    context_methods = []  # Special handling for Context methods
    
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.readlines()
            i = 0
            
            while i < len(lines):
                line = lines[i].strip()
                
                # Extract type with comment
                if line.startswith('type ') and ('struct' in line or 'interface' in line):
                    # Look back for comment
                    comment = ""
                    j = i - 1
                    while j >= 0 and (lines[j].strip().startswith('//') or lines[j].strip() == ''):
                        if lines[j].strip().startswith('//'):
                            comment = lines[j].strip()[2:].strip() + " " + comment
                        j -= 1
                    
                    match = re.match(r'type\s+(\w+)\s+', line)
                    if match:
                        type_name = match.group(1)
                        types_info[type_name] = {
                            'comment': comment.strip(),
                            'methods': []
                        }
                
                # Extract function/method with signature and comment
                if line.startswith('func '):
                    # Look back for comment
                    comment = ""
                    j = i - 1
                    while j >= 0 and (lines[j].strip().startswith('//') or lines[j].strip() == ''):
                        if lines[j].strip().startswith('//'):
                            comment = lines[j].strip()[2:].strip() + " " + comment
                        j -= 1
                    
                    # Extract full signature (may span multiple lines)
                    signature = line
                    k = i + 1
                    while k < len(lines) and '{' not in signature:
                        signature += ' ' + lines[k].strip()
                        k += 1
                    
                    # Remove body
                    if '{' in signature:
                        signature = signature[:signature.index('{')].strip()
                    
                    # Parse receiver if method
                    method_match = re.match(r'func\s+\(([^)]+)\)\s+(\w+)', signature)
                    func_match = re.match(r'func\s+(\w+)', signature)
                    
                    if method_match:
                        receiver = method_match.group(1).strip()
                        func_name = method_match.group(2)
                        # Extract receiver type
                        receiver_type = receiver.split()[-1].strip('*')
                        
                        # Only add if function name is public
                        if func_name[0].isupper():
                            if receiver_type == 'Context':
                                # Special handling for Context methods - add to context_methods
                                context_methods.append({
                                    'name': func_name,
                                    'signature': signature,
                                    'comment': comment.strip()
                                })
                            elif receiver_type in types_info:
                                types_info[receiver_type]['methods'].append({
                                    'name': func_name,
                                    'signature': signature,
                                    'comment': comment.strip()
                                })
                    elif func_match:
                        func_name = func_match.group(1)
                        # Only add if it's public (starts with capital)
                        if func_name[0].isupper():
                            functions_info.append({
                                'name': func_name,
                                'signature': signature,
                                'comment': comment.strip()
                            })
                
                i += 1
            
            # If we have Context methods but no other content, return them as functions
            if context_methods and not types_info and not functions_info:
                functions_info = context_methods
            elif context_methods:
                # Add Context pseudo-type
                types_info['Context'] = {
                    'comment': 'Context methods (receiver omitted for clarity)',
                    'methods': context_methods
                }
                
    except Exception as e:
        print(f"Warning: Could not parse detailed API from {filepath}: {e}")
    
    return types_info, functions_info

def extract_package_comment(filepath):
    """Extract the package-level documentation comment from a Go file."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.readlines()
            comment_lines = []
            in_comment = False
            
            for line in lines:
                stripped = line.strip()
                if stripped.startswith('/*'):
                    in_comment = True
                    comment_lines.append(stripped[2:].strip())
                elif in_comment:
                    if '*/' in stripped:
                        comment_lines.append(stripped.replace('*/', '').strip())
                        break
                    comment_lines.append(stripped.lstrip('*').strip())
                elif stripped.startswith('//'):
                    comment_lines.append(stripped[2:].strip())
                elif stripped.startswith('package'):
                    break
            
            return ' '.join(comment_lines).strip() if comment_lines else None
    except Exception as e:
        return None

def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('-o', '--output-dir',
        dest='output_dir',
        default=OUTPUT_DIR,
        help='Output directory for documentation (default: %(default)s)',
    )
    parser.add_argument('--go-api-path',
        dest='go_api_path',
        default=GO_API_PATH,
        help='Path to Go API source files (default: %(default)s)',
    )
    return parser.parse_args()

def check_go_installed():
    """Check if Go is installed and available."""
    try:
        # Try to find go in common locations
        go_paths = [
            'go',
            'C:\\Program Files\\Go\\bin\\go.exe',
            'C:\\Go\\bin\\go.exe',
        ]
        
        for go_cmd in go_paths:
            try:
                result = subprocess.run([go_cmd, 'version'], 
                                      capture_output=True, 
                                      text=True,
                                      check=True,
                                      timeout=5)
                print(f"Found Go: {result.stdout.strip()}")
                return go_cmd
            except (subprocess.CalledProcessError, FileNotFoundError, subprocess.TimeoutExpired):
                continue
        
        print("WARNING: Go is not installed or not in PATH")
        print("Install Go from https://golang.org/dl/ for enhanced documentation")
        return None
    except Exception as e:
        print(f"WARNING: Could not check Go installation: {e}")
        return None

def extract_package_comment(go_file_path):
    """Extract package-level documentation comment from a Go file."""
    try:
        with open(go_file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
            in_comment = False
            comment_lines = []
            
            for line in lines:
                stripped = line.strip()
                if stripped.startswith('/*'):
                    in_comment = True
                    comment_lines.append(stripped[2:].strip())
                elif in_comment:
                    if stripped.endswith('*/'):
                        comment_lines.append(stripped[:-2].strip())
                        break
                    comment_lines.append(stripped.lstrip('*').strip())
                elif stripped.startswith('//'):
                    comment_lines.append(stripped[2:].strip())
                elif stripped.startswith('package '):
                    break
            
            return ' '.join(comment_lines).strip()
    except Exception as e:
        print(f"Warning: Could not extract comment from {go_file_path}: {e}")
        return ""

def generate_godoc_markdown(go_cmd, go_api_path, output_dir):
    """Generate markdown documentation using godoc."""
    print("Generating documentation with godoc...")
    
    os.makedirs(output_dir, exist_ok=True)
    
    try:
        # Change to the Go API directory
        orig_dir = os.getcwd()
        os.chdir(go_api_path)
        
        # Run go doc to get package documentation
        result = subprocess.run(
            [go_cmd, 'doc', '-all'],
            capture_output=True,
            text=True,
            timeout=30
        )
        
        if result.returncode == 0:
            # Create markdown file
            doc_text = result.stdout
            godoc_md = os.path.join(output_dir, 'godoc.md')
            
            with open(godoc_md, 'w', encoding='utf-8') as f:
                f.write('# Z3 Go API Documentation (godoc)\n\n')
                f.write(doc_text)
            
            print(f"Generated godoc markdown at: {godoc_md}")
            os.chdir(orig_dir)
            return True
        else:
            print(f"godoc returned error: {result.stderr}")
            os.chdir(orig_dir)
            return False
            
    except Exception as e:
        print(f"Error generating godoc markdown: {e}")
        try:
            os.chdir(orig_dir)
        except:
            pass
        return False

def generate_module_page(module_filename, description, go_api_path, output_dir):
    """Generate a detailed HTML page for a single Go module."""
    file_path = os.path.join(go_api_path, module_filename)
    if not os.path.exists(file_path):
        return
    
    module_name = module_filename.replace('.go', '')
    output_path = os.path.join(output_dir, f'{module_name}.html')
    
    # Extract detailed API information
    types_info, functions_info = extract_detailed_api(file_path)
    
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write('<!DOCTYPE html>\n<html lang="en">\n<head>\n')
        f.write('    <meta charset="UTF-8">\n')
        f.write(f'    <title>{module_filename} - Z3 Go API</title>\n')
        f.write('    <style>\n')
        f.write('        body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; margin: 0; padding: 0; line-height: 1.6; }\n')
        f.write('        header { background: #2d3748; color: white; padding: 2rem; }\n')
        f.write('        header h1 { margin: 0; font-size: 2rem; }\n')
        f.write('        header p { margin: 0.5rem 0 0 0; opacity: 0.9; }\n')
        f.write('        .container { max-width: 1200px; margin: 0 auto; padding: 2rem; }\n')
        f.write('        .nav { background: #edf2f7; padding: 1rem; margin-bottom: 2rem; border-radius: 4px; }\n')
        f.write('        .nav a { color: #2b6cb0; text-decoration: none; margin-right: 1rem; }\n')
        f.write('        .nav a:hover { text-decoration: underline; }\n')
        f.write('        h2 { color: #2d3748; border-bottom: 2px solid #4299e1; padding-bottom: 0.5rem; margin-top: 2rem; }\n')
        f.write('        h3 { color: #2d3748; margin-top: 1.5rem; }\n')
        f.write('        .type-section, .function-section { margin: 1.5rem 0; }\n')
        f.write('        .api-item { background: #f7fafc; padding: 1rem; margin: 1rem 0; border-left: 4px solid #4299e1; border-radius: 4px; }\n')
        f.write('        .api-item h4 { margin: 0 0 0.5rem 0; color: #2b6cb0; font-family: monospace; }\n')
        f.write('        .signature { background: #2d3748; color: #e2e8f0; padding: 0.75rem; border-radius: 4px; font-family: monospace; overflow-x: auto; margin: 0.5rem 0; }\n')
        f.write('        .comment { color: #4a5568; margin: 0.5rem 0; }\n')
        f.write('        code { background: #e2e8f0; padding: 2px 6px; border-radius: 3px; font-family: monospace; }\n')
        f.write('        .method-list { margin-left: 1rem; }\n')
        f.write('    </style>\n')
        f.write('</head>\n<body>\n')
        
        f.write('    <header>\n')
        f.write(f'        <h1>{module_filename}</h1>\n')
        f.write(f'        <p>{description}</p>\n')
        f.write('    </header>\n')
        
        f.write('    <div class="container">\n')
        f.write('        <div class="nav">\n')
        f.write('            <a href="index.html">← Back to Index</a>\n')
        f.write('            <a href="godoc.md">Complete API Reference (markdown)</a>\n')
        f.write('            <a href="README.md">README</a>\n')
        f.write('            <a href="../index.html">All Languages</a>\n')
        f.write('        </div>\n')
        
        # Types section
        if types_info:
            f.write('        <h2>Types</h2>\n')
            for type_name in sorted(types_info.keys()):
                type_data = types_info[type_name]
                f.write('        <div class="type-section">\n')
                f.write(f'            <h3>type {type_name}</h3>\n')
                if type_data['comment']:
                    f.write(f'            <p class="comment">{type_data["comment"]}</p>\n')
                
                # Methods
                if type_data['methods']:
                    f.write('            <div class="method-list">\n')
                    f.write('                <h4>Methods:</h4>\n')
                    for method in sorted(type_data['methods'], key=lambda m: m['name']):
                        f.write('                <div class="api-item">\n')
                        f.write(f'                    <h4>{method["name"]}</h4>\n')
                        f.write(f'                    <div class="signature">{method["signature"]}</div>\n')
                        if method['comment']:
                            f.write(f'                    <p class="comment">{method["comment"]}</p>\n')
                        f.write('                </div>\n')
                    f.write('            </div>\n')
                f.write('        </div>\n')
        
        # Package functions section
        if functions_info:
            f.write('        <h2>Functions</h2>\n')
            f.write('        <div class="function-section">\n')
            for func in sorted(functions_info, key=lambda f: f['name']):
                f.write('            <div class="api-item">\n')
                f.write(f'                <h4>{func["name"]}</h4>\n')
                f.write(f'                <div class="signature">{func["signature"]}</div>\n')
                if func['comment']:
                    f.write(f'                <p class="comment">{func["comment"]}</p>\n')
                f.write('            </div>\n')
            f.write('        </div>\n')
        
        if not types_info and not functions_info:
            f.write('        <p><em>No public API documentation extracted. See godoc for complete reference.</em></p>\n')
        
        f.write('        <div class="nav" style="margin-top: 3rem;">\n')
        f.write('            <a href="index.html">← Back to Index</a>\n')
        f.write('        </div>\n')
        f.write('    </div>\n')
        f.write('</body>\n</html>\n')
    
    print(f"Generated module page: {output_path}")

def generate_html_docs(go_api_path, output_dir):
    """Generate HTML documentation for Go bindings."""
    
    # Create output directory
    os.makedirs(output_dir, exist_ok=True)
    
    # Go source files and their descriptions
    go_files = {
        'z3.go': 'Core types (Context, Config, Symbol, Sort, Expr, FuncDecl, Quantifier, Lambda) and basic operations',
        'solver.go': 'Solver and Model API for SMT solving',
        'tactic.go': 'Tactics, Goals, Probes, and Parameters for goal-based solving',
        'arith.go': 'Arithmetic operations (integers, reals) and comparisons',
        'array.go': 'Array operations (select, store, constant arrays)',
        'bitvec.go': 'Bit-vector operations and constraints',
        'fp.go': 'IEEE 754 floating-point operations',
        'seq.go': 'Sequences, strings, and regular expressions',
        'datatype.go': 'Algebraic datatypes, tuples, and enumerations',
        'optimize.go': 'Optimization with maximize/minimize objectives',
        'fixedpoint.go': 'Fixedpoint solver for Datalog and constrained Horn clauses (CHC)',
        'log.go': 'Interaction logging for debugging and analysis',
    }
    
    # Generate main index.html
    index_path = os.path.join(output_dir, 'index.html')
    with open(index_path, 'w', encoding='utf-8') as f:
        f.write('<!DOCTYPE html>\n')
        f.write('<html lang="en">\n')
        f.write('<head>\n')
        f.write('    <meta charset="UTF-8">\n')
        f.write('    <meta name="viewport" content="width=device-width, initial-scale=1.0">\n')
        f.write('    <title>Z3 Go API Documentation</title>\n')
        f.write('    <style>\n')
        f.write('        body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; margin: 0; padding: 0; line-height: 1.6; }\n')
        f.write('        header { background: #2d3748; color: white; padding: 2rem; }\n')
        f.write('        header h1 { margin: 0; font-size: 2.5rem; }\n')
        f.write('        header p { margin: 0.5rem 0 0 0; font-size: 1.1rem; opacity: 0.9; }\n')
        f.write('        .container { max-width: 1200px; margin: 0 auto; padding: 2rem; }\n')
        f.write('        .section { margin: 2rem 0; }\n')
        f.write('        .section h2 { color: #2d3748; border-bottom: 2px solid #4299e1; padding-bottom: 0.5rem; }\n')
        f.write('        .file-list { list-style: none; padding: 0; }\n')
        f.write('        .file-item { background: #f7fafc; border-left: 4px solid #4299e1; margin: 1rem 0; padding: 1rem; border-radius: 4px; }\n')
        f.write('        .file-item h3 { margin: 0 0 0.5rem 0; color: #2d3748; }\n')
        f.write('        .file-item h3 a { color: #2b6cb0; text-decoration: none; }\n')
        f.write('        .file-item h3 a:hover { color: #4299e1; text-decoration: underline; }\n')
        f.write('        .file-item p { margin: 0; color: #4a5568; }\n')
        f.write('        .code-block { background: #2d3748; color: #e2e8f0; padding: 1.5rem; border-radius: 4px; overflow-x: auto; }\n')
        f.write('        .code-block pre { margin: 0; }\n')
        f.write('        .install-section { background: #edf2f7; padding: 1.5rem; border-radius: 4px; margin: 1rem 0; }\n')
        f.write('        .back-link { display: inline-block; margin-top: 2rem; color: #2b6cb0; text-decoration: none; }\n')
        f.write('        .back-link:hover { text-decoration: underline; }\n')
        f.write('    </style>\n')
        f.write('</head>\n')
        f.write('<body>\n')
        
        f.write('    <header>\n')
        f.write('        <h1>Z3 Go API Documentation</h1>\n')
        f.write('        <p>Go bindings for the Z3 Theorem Prover</p>\n')
        f.write('    </header>\n')
        
        f.write('    <div class="container">\n')
        
        # Overview section
        f.write('        <div class="section">\n')
        f.write('            <h2>Overview</h2>\n')
        f.write('            <p>The Z3 Go bindings provide idiomatic Go access to the Z3 SMT solver. These bindings use CGO to wrap the Z3 C API and provide automatic memory management through Go finalizers.</p>\n')
        f.write('            <p><strong>Package:</strong> <code>github.com/Z3Prover/z3/src/api/go</code></p>\n')
        f.write('        </div>\n')
        
        # Quick start
        f.write('        <div class="section">\n')
        f.write('            <h2>Quick Start</h2>\n')
        f.write('            <div class="code-block">\n')
        f.write('                <pre>package main\n\n')
        f.write('import (\n')
        f.write('    "fmt"\n')
        f.write('    "github.com/Z3Prover/z3/src/api/go"\n')
        f.write(')\n\n')
        f.write('func main() {\n')
        f.write('    // Create a context\n')
        f.write('    ctx := z3.NewContext()\n\n')
        f.write('    // Create integer variable\n')
        f.write('    x := ctx.MkIntConst("x")\n\n')
        f.write('    // Create solver\n')
        f.write('    solver := ctx.NewSolver()\n\n')
        f.write('    // Add constraint: x > 0\n')
        f.write('    zero := ctx.MkInt(0, ctx.MkIntSort())\n')
        f.write('    solver.Assert(ctx.MkGt(x, zero))\n\n')
        f.write('    // Check satisfiability\n')
        f.write('    if solver.Check() == z3.Satisfiable {\n')
        f.write('        fmt.Println("sat")\n')
        f.write('        model := solver.Model()\n')
        f.write('        if val, ok := model.Eval(x, true); ok {\n')
        f.write('            fmt.Println("x =", val.String())\n')
        f.write('        }\n')
        f.write('    }\n')
        f.write('}</pre>\n')
        f.write('            </div>\n')
        f.write('        </div>\n')
        
        # Installation
        f.write('        <div class="section">\n')
        f.write('            <h2>Installation</h2>\n')
        f.write('            <div class="install-section">\n')
        f.write('                <p><strong>Prerequisites:</strong></p>\n')
        f.write('                <ul>\n')
        f.write('                    <li>Go 1.20 or later</li>\n')
        f.write('                    <li>Z3 built as a shared library</li>\n')
        f.write('                    <li>CGO enabled (default)</li>\n')
        f.write('                </ul>\n')
        f.write('                <p><strong>Build Z3 with Go bindings:</strong></p>\n')
        f.write('                <div class="code-block">\n')
        f.write('                    <pre># Using CMake\n')
        f.write('mkdir build && cd build\n')
        f.write('cmake -DZ3_BUILD_GO_BINDINGS=ON -DZ3_BUILD_LIBZ3_SHARED=ON ..\n')
        f.write('make\n\n')
        f.write('# Using Python build script\n')
        f.write('python scripts/mk_make.py --go\n')
        f.write('cd build && make</pre>\n')
        f.write('                </div>\n')
        f.write('                <p><strong>Set environment variables:</strong></p>\n')
        f.write('                <div class="code-block">\n')
        f.write('                    <pre>export CGO_CFLAGS="-I${Z3_ROOT}/src/api"\n')
        f.write('export CGO_LDFLAGS="-L${Z3_ROOT}/build -lz3"\n')
        f.write('export LD_LIBRARY_PATH="${Z3_ROOT}/build:$LD_LIBRARY_PATH"</pre>\n')
        f.write('                </div>\n')
        f.write('            </div>\n')
        f.write('        </div>\n')
        
        # API modules with detailed documentation
        f.write('        <div class="section">\n')
        f.write('            <h2>API Modules</h2>\n')
        
        for filename, description in go_files.items():
            file_path = os.path.join(go_api_path, filename)
            if os.path.exists(file_path):
                module_name = filename.replace('.go', '')
                
                # Generate individual module page
                generate_module_page(filename, description, go_api_path, output_dir)
                
                # Extract types and functions from the file
                types, functions = extract_types_and_functions(file_path)
                
                f.write(f'            <div class="file-item" id="{module_name}">\n')
                f.write(f'                <h3><a href="{module_name}.html">{filename}</a></h3>\n')
                f.write(f'                <p>{description}</p>\n')
                
                if types:
                    f.write('                <p><strong>Types:</strong> ')
                    f.write(', '.join([f'<code>{t}</code>' for t in sorted(types)]))
                    f.write('</p>\n')
                
                if functions:
                    # Filter public functions
                    public_funcs = [f for f in functions if f and len(f) > 0 and f[0].isupper()]
                    if public_funcs:
                        f.write('                <p><strong>Key Functions:</strong> ')
                        # Show first 15 functions to keep it manageable
                        funcs_to_show = sorted(public_funcs)[:15]
                        f.write(', '.join([f'<code>{func}()</code>' for func in funcs_to_show]))
                        if len(public_funcs) > 15:
                            f.write(f' <em>(+{len(public_funcs)-15} more)</em>')
                        f.write('</p>\n')
                
                f.write(f'                <p><a href="{module_name}.html">→ View full API reference</a></p>\n')
                f.write('            </div>\n')
        
        f.write('        </div>\n')
        
        # Features section
        f.write('        <div class="section">\n')
        f.write('            <h2>Features</h2>\n')
        f.write('            <ul>\n')
        f.write('                <li><strong>Core SMT:</strong> Boolean logic, arithmetic, arrays, quantifiers</li>\n')
        f.write('                <li><strong>Bit-vectors:</strong> Fixed-size bit-vector arithmetic and operations</li>\n')
        f.write('                <li><strong>Floating-point:</strong> IEEE 754 floating-point arithmetic</li>\n')
        f.write('                <li><strong>Strings & Sequences:</strong> String constraints and sequence operations</li>\n')
        f.write('                <li><strong>Regular Expressions:</strong> Pattern matching and regex constraints</li>\n')
        f.write('                <li><strong>Datatypes:</strong> Algebraic datatypes, tuples, enumerations</li>\n')
        f.write('                <li><strong>Tactics:</strong> Goal-based solving with tactic combinators</li>\n')
        f.write('                <li><strong>Optimization:</strong> MaxSMT with maximize/minimize objectives</li>\n')
        f.write('                <li><strong>Memory Management:</strong> Automatic via Go finalizers</li>\n')
        f.write('            </ul>\n')
        f.write('        </div>\n')
        
        # Resources
        f.write('        <div class="section">\n')
        f.write('            <h2>Resources</h2>\n')
        f.write('            <ul>\n')
        f.write('                <li><a href="https://github.com/Z3Prover/z3">Z3 GitHub Repository</a></li>\n')
        f.write('                <li><a href="../index.html">All API Documentation</a></li>\n')
        
        # Check if README exists and copy it
        readme_path = os.path.join(go_api_path, 'README.md')
        if os.path.exists(readme_path):
            # Copy README.md to output directory
            readme_dest = os.path.join(output_dir, 'README.md')
            try:
                import shutil
                shutil.copy2(readme_path, readme_dest)
                f.write('                <li><a href="README.md">Go API README (markdown)</a></li>\n')
                print(f"Copied README.md to: {readme_dest}")
            except Exception as e:
                print(f"Warning: Could not copy README.md: {e}")
        
        # Link to godoc.md if it will be generated
        f.write('                <li><a href="godoc.md">Complete API Reference (godoc markdown)</a></li>\n')
        
        f.write('            </ul>\n')
        f.write('        </div>\n')
        
        f.write('        <a href="../index.html" class="back-link">← Back to main API documentation</a>\n')
        f.write('    </div>\n')
        f.write('</body>\n')
        f.write('</html>\n')
    
    print(f"Generated Go documentation index at: {index_path}")
    return True

def main():
    args = parse_args()
    
    print("Z3 Go API Documentation Generator")
    print("=" * 50)
    
    # Check if Go is installed
    go_cmd = check_go_installed()
    
    # Verify Go API path exists
    if not os.path.exists(args.go_api_path):
        print(f"ERROR: Go API path does not exist: {args.go_api_path}")
        return 1
    
    # Generate documentation
    print(f"\nGenerating documentation from: {args.go_api_path}")
    print(f"Output directory: {args.output_dir}")
    
    # Try godoc first if Go is available
    godoc_success = False
    if go_cmd:
        godoc_success = generate_godoc_markdown(go_cmd, args.go_api_path, args.output_dir)
    
    # Always generate our custom HTML documentation
    if not generate_html_docs(args.go_api_path, args.output_dir):
        print("ERROR: Failed to generate documentation")
        return 1
    
    if godoc_success:
        print("\n✓ Generated both godoc markdown and custom HTML documentation")
    
    print("\n" + "=" * 50)
    print("Documentation generated successfully!")
    print(f"Open {os.path.join(args.output_dir, 'index.html')} in your browser.")
    
    return 0

if __name__ == '__main__':
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\nInterrupted by user")
        sys.exit(1)
    except Exception as e:
        print(f"ERROR: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
