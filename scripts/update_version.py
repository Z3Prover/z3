#!/usr/bin/env python3
"""
Helper script to update version in all Z3 files when VERSION.txt changes.

This script reads VERSION.txt and updates the remaining hardcoded version references
that cannot be automatically read from VERSION.txt due to limitations in their
respective build systems.

Usage: python scripts/update_version.py
"""

import os
import re
import sys

def read_version():
    """Read version from VERSION.txt file."""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    version_file = os.path.join(script_dir, 'VERSION.txt')
    
    try:
        with open(version_file, 'r') as f:
            version = f.read().strip()
        return version
    except IOError as e:
        print(f"Error reading VERSION.txt: {e}")
        sys.exit(1)

def update_bazel_module(version):
    """Update MODULE.bazel with the version."""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    module_file = os.path.join(os.path.dirname(script_dir), 'MODULE.bazel')
    
    # Extract major.minor.patch from major.minor.patch.tweak
    version_parts = version.split('.')
    if len(version_parts) >= 3:
        bazel_version = f"{version_parts[0]}.{version_parts[1]}.{version_parts[2]}"
    else:
        bazel_version = version
    
    try:
        with open(module_file, 'r') as f:
            content = f.read()
        
        # Update version line in module() block only
        content = re.sub(
            r'(module\([^)]*?\s+version\s*=\s*")[^"]*(".*?)',
            r'\g<1>' + bazel_version + r'\g<2>',
            content,
            flags=re.DOTALL
        )
        
        with open(module_file, 'w') as f:
            f.write(content)
        
        print(f"Updated MODULE.bazel version to {bazel_version}")
    except IOError as e:
        print(f"Error updating MODULE.bazel: {e}")

def update_nightly_yaml(version):
    """Update scripts/nightly.yaml with the version."""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    nightly_file = os.path.join(script_dir, 'nightly.yaml')
    
    version_parts = version.split('.')
    if len(version_parts) >= 3:
        major, minor, patch = version_parts[0], version_parts[1], version_parts[2]
    else:
        print(f"Warning: Invalid version format in VERSION.txt: {version}")
        return
    
    try:
        with open(nightly_file, 'r') as f:
            content = f.read()
        
        # Update Major, Minor, Patch variables
        content = re.sub(r"(\s+Major:\s*')[^']*('.*)", r"\g<1>" + major + r"\g<2>", content)
        content = re.sub(r"(\s+Minor:\s*')[^']*('.*)", r"\g<1>" + minor + r"\g<2>", content)
        content = re.sub(r"(\s+Patch:\s*')[^']*('.*)", r"\g<1>" + patch + r"\g<2>", content)
        
        with open(nightly_file, 'w') as f:
            f.write(content)
        
        print(f"Updated nightly.yaml version to {major}.{minor}.{patch}")
    except IOError as e:
        print(f"Error updating nightly.yaml: {e}")

def update_release_yml(version):
    """Update scripts/release.yml with the version."""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    release_file = os.path.join(script_dir, 'release.yml')
    
    # Extract major.minor.patch from major.minor.patch.tweak
    version_parts = version.split('.')
    if len(version_parts) >= 3:
        release_version = f"{version_parts[0]}.{version_parts[1]}.{version_parts[2]}"
    else:
        release_version = version
    
    try:
        with open(release_file, 'r') as f:
            content = f.read()
        
        # Update ReleaseVersion variable
        content = re.sub(
            r"(\s+ReleaseVersion:\s*')[^']*('.*)",
            r"\g<1>" + release_version + r"\g<2>",
            content
        )
        
        with open(release_file, 'w') as f:
            f.write(content)
        
        print(f"Updated release.yml version to {release_version}")
    except IOError as e:
        print(f"Error updating release.yml: {e}")

def update_github_nightly_yml(version):
    """Update .github/workflows/nightly.yml with the version."""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    nightly_file = os.path.join(os.path.dirname(script_dir), '.github', 'workflows', 'nightly.yml')
    
    version_parts = version.split('.')
    if len(version_parts) >= 3:
        major, minor, patch = version_parts[0], version_parts[1], version_parts[2]
    else:
        print(f"Warning: Invalid version format in VERSION.txt: {version}")
        return
    
    try:
        with open(nightly_file, 'r') as f:
            content = f.read()
        
        # Update MAJOR, MINOR, PATCH environment variables
        content = re.sub(r"(\s+MAJOR:\s*')[^']*('.*)", r"\g<1>" + major + r"\g<2>", content)
        content = re.sub(r"(\s+MINOR:\s*')[^']*('.*)", r"\g<1>" + minor + r"\g<2>", content)
        content = re.sub(r"(\s+PATCH:\s*')[^']*('.*)", r"\g<1>" + patch + r"\g<2>", content)
        
        with open(nightly_file, 'w') as f:
            f.write(content)
        
        print(f"Updated .github/workflows/nightly.yml version to {major}.{minor}.{patch}")
    except IOError as e:
        print(f"Error updating .github/workflows/nightly.yml: {e}")

def main():
    """Main function."""
    print("Z3 Version Update Script")
    print("========================")
    
    version = read_version()
    print(f"Read version from VERSION.txt: {version}")
    
    print("\nUpdating files that cannot auto-read VERSION.txt...")
    
    update_bazel_module(version)
    update_nightly_yaml(version)
    update_release_yml(version)
    update_github_nightly_yml(version)
    
    print("\nUpdate complete!")
    print("\nNote: The following files automatically read from VERSION.txt:")
    print("  - CMakeLists.txt")
    print("  - scripts/mk_project.py")
    print("\nThese do not need manual updates.")

if __name__ == "__main__":
    main()