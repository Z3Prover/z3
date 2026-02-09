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
    # VERSION.txt is now in scripts directory
    version_file = os.path.join(script_dir, 'VERSION.txt')
    
    if not os.path.exists(version_file):
        print(f"VERSION.txt not found at {version_file}")
        sys.exit(1)
    
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


def update_github_nightly_yml(version):
    """Update .github/workflows/nightly.yml with the version."""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    nightly_file = os.path.join(os.path.dirname(script_dir), '.github', 'workflows', 'nightly.yml')
    
    if not os.path.exists(nightly_file):
        print(f"Warning: {nightly_file} does not exist, skipping")
        return
    
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


def update_github_nuget_build_yml(version):
    """Update .github/workflows/nuget-build.yml example version and default."""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    nuget_build_file = os.path.join(os.path.dirname(script_dir), '.github', 'workflows', 'nuget-build.yml')
    
    if not os.path.exists(nuget_build_file):
        print(f"Warning: {nuget_build_file} does not exist, skipping")
        return
    
    version_parts = version.split('.')
    if len(version_parts) >= 3:
        display_version = f"{version_parts[0]}.{version_parts[1]}.{version_parts[2]}"
    else:
        display_version = version
    
    try:
        with open(nuget_build_file, 'r') as f:
            content = f.read()
        
        # Update example version in description and default value
        content = re.sub(
            r"(description:\s*'Version number for the NuGet package \(e\.g\.,\s*)[0-9]+\.[0-9]+\.[0-9]+(\)')",
            r"\g<1>" + display_version + r"\g<2>",
            content
        )
        content = re.sub(
            r"(default:\s*')[0-9]+\.[0-9]+\.[0-9]+(')",
            r"\g<1>" + display_version + r"\g<2>",
            content
        )
        # Update fallback versions in assembly-version parameters
        content = re.sub(
            r"(\|\|\s*')[0-9]+\.[0-9]+\.[0-9]+(')",
            r"\g<1>" + display_version + r"\g<2>",
            content
        )
        
        with open(nuget_build_file, 'w') as f:
            f.write(content)
        
        print(f"Updated .github/workflows/nuget-build.yml version references to {display_version}")
    except IOError as e:
        print(f"Error updating .github/workflows/nuget-build.yml: {e}")



def update_github_release_yml(version):
    """Update .github/workflows/release.yml release_version input default and description example."""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    release_file = os.path.join(os.path.dirname(script_dir), '.github', 'workflows', 'release.yml')
    
    if not os.path.exists(release_file):
        print(f"Warning: {release_file} does not exist, skipping")
        return
    
    version_parts = version.split('.')
    if len(version_parts) >= 3:
        display_version = f"{version_parts[0]}.{version_parts[1]}.{version_parts[2]}"
    else:
        display_version = version
    
    try:
        with open(release_file, 'r') as f:
            content = f.read()
        
        # Update RELEASE_VERSION environment variable and input parameter default
        # Handle both quoted values and input parameter references
        content = re.sub(
            r"(\s+RELEASE_VERSION:\s*')([^']*)'",
            r"\g<1>" + display_version + "'",
            content
        )
        content = re.sub(
            r"(\s+RELEASE_VERSION:\s*)\$\{\{\s*github\.event\.inputs\.release_version\s*\}\}",
            r"\g<1>'" + display_version + "'",
            content
        )
        
        # Update example version in release_version input description  
        content = re.sub(
            r"(description:\s*'Release version \(e\.g\.,\s*)[0-9]+\.[0-9]+\.[0-9]+(\)')",
            r"\g<1>" + display_version + r"\g<2>",
            content
        )
        
        # Add or update default value for release_version input parameter
        # Look for the release_version input section and add/update default
        lines = content.split('\n')
        in_release_version_input = False
        for i, line in enumerate(lines):
            if 'release_version:' in line and 'inputs:' in lines[max(0, i-5):i]:
                in_release_version_input = True
            elif in_release_version_input:
                if line.strip().startswith('default:'):
                    # Update existing default
                    lines[i] = re.sub(r"(default:\s*')([^']*)'", r"\g<1>" + display_version + "'", line)
                    lines[i] = re.sub(r"(default:\s*)('[^']*'|[0-9.]+)", r"\g<1>'" + display_version + "'", line)
                    in_release_version_input = False
                    break
                elif line.strip() and not line.startswith('    ') and not line.startswith('\t'):
                    # We've moved to the next input, insert default before this line
                    lines.insert(i, f"        default: '{display_version}'")
                    in_release_version_input = False
                    break
                elif i == len(lines) - 1:
                    # End of file, add default
                    lines.insert(i, f"        default: '{display_version}'")
                    break
        
        content = '\n'.join(lines)
        
        # Update example version in description
        content = re.sub(
            r"(description:\s*'Release version \(e\.g\.,\s*)[0-9]+\.[0-9]+\.[0-9]+(\)')",
            r"\g<1>" + display_version + r"\g<2>",
            content
        )
        
        with open(release_file, 'w') as f:
            f.write(content)
        
        print(f"Updated .github/workflows/release.yml input parameter default and example version to {display_version}")
    except IOError as e:
        print(f"Error updating .github/workflows/release.yml: {e}")

def main():
    """Main function."""
    print("Z3 Version Update Script")
    print("========================")
    
    version = read_version()
    print(f"Read version from VERSION.txt: {version}")
    
    print("\nUpdating files that cannot auto-read VERSION.txt...")
    
    update_bazel_module(version)
    update_github_nightly_yml(version)
    update_github_release_yml(version)
    update_github_nuget_build_yml(version)
    
    print("\nUpdate complete!")
    print("\nNote: The following files automatically read from VERSION.txt:")
    print("  - CMakeLists.txt")
    print("  - scripts/mk_project.py")
    print("\nThese do not need manual updates.")
    print("\nNote: .github/workflows/release.yml uses input parameters for actual releases,")
    print("but the release_version input parameter default and example version in the description have been updated.")

if __name__ == "__main__":
    main()