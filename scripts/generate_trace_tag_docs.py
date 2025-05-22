# generate_trace_tag_docs.py
# This script generates a Markdown file from the trace_tags.def file.
# It extracts the trace tags and their descriptions and formats them into a table.
# The generated Markdown file can be used for documentation purposes.

# Trace Tags Documentation

# | Tag | Description |
# |-----|-------------|
# | `mam_int` | mam initialization |
# | `mam_test` | mam test |
# | `propagate` | propagation |

import re

def_file = "./src/util/trace_tags.def"
output_md = "./trace_tags.md"

with open(def_file, "r") as f:
    lines = f.readlines()

entries = []
for line in lines:
    match = re.match(r'X\(\s*(\w+)\s*,\s*"([^"]+)"\s*\)', line)
    if match:
        tag, desc = match.groups()
        entries.append((tag, desc))

with open(output_md, "w") as f:
    f.write("# Trace Tags Documentation\n\n")
    f.write("| Tag | Description |\n")
    f.write("|-----|-------------|\n")
    for tag, desc in entries:
        f.write(f"| `{tag}` | {desc} |\n")

