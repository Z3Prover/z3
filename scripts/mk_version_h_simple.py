"""
Create a copy of util/z3_version.h that is solely based on the contents of
scripts/VERSION.txt, and not the commit hash of the current source
checkout. This is used when building Z3 through Bazel.
"""

import sys

with open(sys.argv[1]) as f:
    version = f.read().strip()
    version_parts = version.split(".")
with open(sys.argv[2], "w") as f:
    f.write(f"""
#define Z3_MAJOR_VERSION {version_parts[0]}
#define Z3_MINOR_VERSION {version_parts[1]}
#define Z3_BUILD_NUMBER {version_parts[2]}
#define Z3_REVISION_NUMBER {version_parts[3]}
#define Z3_FULL_VERSION "Z3 {version}"
""")
