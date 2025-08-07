#!/usr/bin/env python3
"""
sus.py: Search for function calls with three function-call arguments (ambiguous parameter evaluation order)
and print matches in grep-like format: file:line:match
"""
import os
import re
# skip chain calls like obj.method(...)
chain_pattern = re.compile(r"\.\s*[A-Za-z_]\w*\s*\(")

# pattern: identifier(... foo(...), ... bar(...)) with two function-call args
pattern = re.compile(
    r"\b[A-Za-z_]\w*"             # function name
    r"\s*\(\s*"                 # '('
    r"[^)]*?[A-Za-z_]\w*\([^)]*\)"  # first func-call arg anywhere
    r"[^)]*?,[^)]*?[A-Za-z_]\w*\([^)]*\)"  # second func-call arg
    r"[^)]*?\)"                   # up to closing ')'
)

# file extensions to include
excl = ('TRACE', 'ASSERT', 'VERIFY', )

for root, dirs, files in os.walk('src/smt'):
    # skip hidden dirs
    dirs[:] = [d for d in dirs if not d.startswith('.')]
    for file in files:
        path = os.path.join(root, file)
        try:
            with open(path, 'r', encoding='utf-8', errors='ignore') as f:
                for i, line in enumerate(f, 1):
                    if pattern.search(line):
                        # skip lines with TRACE or ASSERT in all caps
                        if 'TRACE' in line or 'ASSERT' in line or 'VERIFY' in line:
                            continue
                        # skip chain calls (method-style chaining)
                        if chain_pattern.search(line):
                            continue
                        full_path = os.path.abspath(path)
                        print(f"{full_path}:{i}:{line.rstrip()}")
        except OSError:
            pass
