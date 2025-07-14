#!/usr/bin/env python3
"""
Demonstration script showing that the dist-info fix works.
This script validates that z3-solver can be detected by downstream packages.
"""

import subprocess
import sys
import tempfile
import os
from pathlib import Path

def demonstrate_fix():
    """Demonstrate that the fix allows proper package detection."""
    print("=" * 60)
    print("Demonstrating z3-solver dist-info fix")
    print("=" * 60)
    
    # Show that the package is properly installed with dist-info
    try:
        import importlib.metadata as metadata
        dist = metadata.distribution('z3-solver')
        print(f"✓ Package detectable: {dist.name} v{dist.version}")
        print(f"  Location: {dist.locate_file('.')}")
        print(f"  Has {len(list(dist.files)) if dist.files else 0} files")
    except metadata.PackageNotFoundError:
        print("✗ Package not found by importlib.metadata")
        return False
    
    # Test pip detection
    result = subprocess.run([sys.executable, '-m', 'pip', 'show', 'z3-solver'], 
                           capture_output=True, text=True)
    if result.returncode == 0:
        print("✓ Package detectable by pip show")
        for line in result.stdout.split('\n'):
            if line.startswith(('Name:', 'Version:', 'Location:')):
                print(f"  {line}")
    else:
        print("✗ Package not detectable by pip show")
        return False
    
    # Find the actual dist-info directory
    import site
    site_packages_dirs = site.getsitepackages()
    if hasattr(site, 'getusersitepackages'):
        site_packages_dirs.append(site.getusersitepackages())
    
    # Also check current environment
    try:
        import z3
        z3_path = Path(z3.__file__).parent.parent
        site_packages_dirs.append(str(z3_path))
    except ImportError:
        pass
    
    dist_info_found = False
    for site_dir in site_packages_dirs:
        site_path = Path(site_dir)
        if site_path.exists():
            dist_info_dirs = list(site_path.glob("z3_solver*.dist-info"))
            if dist_info_dirs:
                dist_info_dir = dist_info_dirs[0]
                print(f"✓ Found dist-info directory: {dist_info_dir}")
                
                # Check contents
                metadata_file = dist_info_dir / "METADATA"
                if metadata_file.exists():
                    print(f"✓ METADATA file exists: {metadata_file}")
                    with open(metadata_file) as f:
                        content = f.read()
                        if "Name: z3-solver" in content:
                            print("✓ METADATA contains correct package name")
                        else:
                            print("✗ METADATA missing correct package name")
                            return False
                else:
                    print("✗ METADATA file missing")
                    return False
                    
                # List all files in dist-info
                print("  dist-info contents:")
                for item in sorted(dist_info_dir.iterdir()):
                    print(f"    {item.name}")
                    
                dist_info_found = True
                break
    
    if not dist_info_found:
        print("✗ No dist-info directory found")
        return False
    
    # Simulate what a downstream package would do
    print("\n" + "=" * 60)
    print("Simulating downstream package detection")
    print("=" * 60)
    
    downstream_check = '''
import sys
try:
    import pkg_resources
    try:
        pkg_resources.get_distribution("z3-solver")
        print("✓ pkg_resources can find z3-solver")
    except pkg_resources.DistributionNotFound:
        print("✗ pkg_resources cannot find z3-solver")
        sys.exit(1)
    
    import importlib.metadata as metadata
    try:
        metadata.distribution("z3-solver")
        print("✓ importlib.metadata can find z3-solver")
    except metadata.PackageNotFoundError:
        print("✗ importlib.metadata cannot find z3-solver")
        sys.exit(1)
        
    print("✓ All downstream detection methods work!")
    
except Exception as e:
    print(f"✗ Error in downstream detection: {e}")
    sys.exit(1)
'''
    
    result = subprocess.run([sys.executable, '-c', downstream_check], 
                           capture_output=True, text=True)
    if result.returncode == 0:
        print(result.stdout.strip())
    else:
        print("✗ Downstream detection failed:")
        print(result.stderr.strip())
        return False
    
    print("\n" + "=" * 60)
    print("SUCCESS: z3-solver dist-info fix is working correctly!")
    print("Downstream packages can now detect z3-solver installation.")
    print("=" * 60)
    return True

if __name__ == "__main__":
    success = demonstrate_fix()
    sys.exit(0 if success else 1)