#!/usr/bin/env python3
"""
Add godoc comments to Z3 Go bindings systematically.
This script adds proper godoc documentation to all exported types and functions.
"""

import os
import re

# Godoc comment templates for common patterns
TYPE_COMMENTS = {
    'Config': '// Config represents a Z3 configuration object used to customize solver behavior.\n// Create with NewConfig and configure using SetParamValue before creating a Context.',
    'Context': '// Context represents a Z3 logical context.\n// All Z3 objects (sorts, expressions, solvers) are tied to the context that created them.\n// Contexts are not thread-safe - use separate contexts for concurrent operations.',
    'Symbol': '// Symbol represents a Z3 symbol, which can be either a string or integer identifier.\n// Symbols are used to name sorts, constants, and functions.',
    'AST': '// AST represents an Abstract Syntax Tree node in Z3.\n// This is the base type for all Z3 expressions, sorts, and function declarations.',
    'Sort': '// Sort represents a type in Z3\'s type system.\n// Common sorts include Bool, Int, Real, BitVec, Array, and user-defined datatypes.',
    'Expr': '// Expr represents a Z3 expression (term).\n// Expressions are typed AST nodes that can be evaluated, simplified, or used in constraints.',
    'FuncDecl': '// FuncDecl represents a function declaration in Z3.\n// Function declarations define the signature (domain and range sorts) of functions.',
    'Pattern': '// Pattern represents a pattern for quantifier instantiation.\n// Patterns guide Z3\'s E-matching algorithm for quantifier instantiation.',
    'Quantifier': '// Quantifier represents a quantified formula (forall or exists).\n// Quantifiers bind variables and include optional patterns for instantiation.',
    'Lambda': '// Lambda represents a lambda expression (anonymous function).\n// Lambda expressions can be used as array values or in higher-order reasoning.',
    'Statistics': '// Statistics holds performance and diagnostic information from Z3 solvers.\n// Use GetKey, GetUintValue, and GetDoubleValue to access individual statistics.',
}

FUNCTION_COMMENTS = {
    'NewConfig': '// NewConfig creates a new Z3 configuration object.\n// Use SetParamValue to configure parameters before creating a context.',
    'NewContext': '// NewContext creates a new Z3 context with default configuration.\n// The context manages memory for all Z3 objects and must outlive any objects it creates.',
    'NewContextWithConfig': '// NewContextWithConfig creates a new Z3 context with the given configuration.\n// The configuration is consumed and should not be reused.',
}

def add_godoc_comment(content, pattern, comment):
    """Add godoc comment before a type or function declaration."""
    # Check if comment already exists
    lines = content.split('\n')
    result = []
    i = 0
    
    while i < len(lines):
        line = lines[i]
        
        # Check if this line matches our pattern
        if re.match(pattern, line):
            # Check if previous line is already a comment
            if i > 0 and (result[-1].strip().startswith('//') or result[-1].strip().startswith('/*')):
                # Comment exists, skip
                result.append(line)
            else:
                # Add comment
                result.append(comment)
                result.append(line)
        else:
            result.append(line)
        
        i += 1
    
    return '\n'.join(result)

def process_file(filepath, type_comments, func_comments):
    """Process a single Go file and add godoc comments."""
    print(f"Processing {filepath}...")
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Add type comments
    for type_name, comment in type_comments.items():
        pattern = f'^type {type_name} struct'
        content = add_godoc_comment(content, pattern, comment)
    
    # Add function comments
    for func_name, comment in func_comments.items():
        pattern = f'^func (\\([^)]+\\) )?{func_name}\\('
        content = add_godoc_comment(content, pattern, comment)
    
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(content)
    
    print(f"Updated {filepath}")

if __name__ == '__main__':
    go_api_dir = os.path.dirname(os.path.abspath(__file__))
    
    # Process z3.go with core types
    z3_go = os.path.join(go_api_dir, 'z3.go')
    if os.path.exists(z3_go):
        process_file(z3_go, TYPE_COMMENTS, FUNCTION_COMMENTS)
    
    print("\nGodoc comments added successfully!")
    print("Run 'go doc' to verify documentation.")
