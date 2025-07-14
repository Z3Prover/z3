#!/usr/bin/env python3
"""
Test script to validate that z3-solver creates dist-info when installed from source.
This test ensures that downstream packages can detect z3-solver properly.
"""

import subprocess
import sys
import tempfile
import os
import shutil
from pathlib import Path

def test_source_install_creates_dist_info():
    """Test that installing z3-solver from source creates dist-info directory."""
    print("Testing that source installation creates dist-info...")
    
    # Create a temporary virtual environment
    with tempfile.TemporaryDirectory() as tmpdir:
        venv_path = Path(tmpdir) / "test_venv"
        
        # Create virtual environment
        result = subprocess.run([sys.executable, "-m", "venv", str(venv_path)], 
                               capture_output=True, text=True)
        if result.returncode != 0:
            print(f"Failed to create venv: {result.stderr}")
            return False
            
        # Determine the path to pip in the virtual environment
        if sys.platform == "win32":
            pip_path = venv_path / "Scripts" / "pip.exe"
            python_path = venv_path / "Scripts" / "python.exe"
        else:
            pip_path = venv_path / "bin" / "pip"
            python_path = venv_path / "bin" / "python"
            
        # Upgrade pip and setuptools
        result = subprocess.run([str(pip_path), "install", "--upgrade", "pip", "setuptools"],
                               capture_output=True, text=True)
        if result.returncode != 0:
            print(f"Failed to upgrade pip/setuptools: {result.stderr}")
            return False
            
        # Get the path to the z3 python package
        z3_python_path = Path(__file__).parent.absolute()
        
        # Install z3-solver in editable mode without deps to avoid building C++ components
        result = subprocess.run([str(pip_path), "install", "--no-deps", "--no-build-isolation", 
                                "-e", str(z3_python_path)],
                               capture_output=True, text=True)
        if result.returncode != 0:
            print(f"Failed to install z3-solver: {result.stderr}")
            return False
            
        # Check that dist-info directory was created
        site_packages = venv_path / "lib" / f"python{sys.version_info.major}.{sys.version_info.minor}" / "site-packages"
        if sys.platform == "win32":
            site_packages = venv_path / "Lib" / "site-packages"
            
        dist_info_dirs = list(site_packages.glob("z3_solver*.dist-info"))
        if not dist_info_dirs:
            print(f"ERROR: No dist-info directory found in {site_packages}")
            print("Available directories:")
            for item in site_packages.iterdir():
                if item.is_dir():
                    print(f"  {item.name}")
            return False
            
        dist_info_dir = dist_info_dirs[0]
        print(f"SUCCESS: Found dist-info directory: {dist_info_dir.name}")
        
        # Check that the METADATA file exists and has proper content
        metadata_file = dist_info_dir / "METADATA"
        if not metadata_file.exists():
            print(f"ERROR: METADATA file not found in {dist_info_dir}")
            return False
            
        metadata_content = metadata_file.read_text()
        if "Name: z3-solver" not in metadata_content:
            print(f"ERROR: METADATA file doesn't contain expected package name")
            return False
            
        print("SUCCESS: METADATA file contains correct package information")
        
        # Test that the package can be detected by pip
        result = subprocess.run([str(pip_path), "show", "z3-solver"],
                               capture_output=True, text=True)
        if result.returncode != 0:
            print(f"ERROR: pip show z3-solver failed: {result.stderr}")
            return False
            
        if "Name: z3-solver" not in result.stdout:
            print(f"ERROR: pip show output doesn't contain expected package name")
            return False
            
        print("SUCCESS: pip can detect the installed package")
        
        # Test that Python can detect the package
        python_test_script = '''
import sys
try:
    import importlib.metadata as metadata
    dist = metadata.distribution("z3-solver")
    print(f"Found package: {dist.name} {dist.version}")
    sys.exit(0)
except metadata.PackageNotFoundError:
    print("ERROR: Package not found by importlib.metadata")
    sys.exit(1)
'''
        
        result = subprocess.run([str(python_path), "-c", python_test_script],
                               capture_output=True, text=True)
        if result.returncode != 0:
            print(f"ERROR: Python package detection failed: {result.stderr}")
            return False
            
        print("SUCCESS: Python can detect the installed package")
        print(f"Detection output: {result.stdout.strip()}")
        
        return True

if __name__ == "__main__":
    success = test_source_install_creates_dist_info()
    if success:
        print("\n✓ All tests passed! Source installation creates proper dist-info.")
        sys.exit(0)
    else:
        print("\n✗ Test failed! Source installation does not create proper dist-info.")
        sys.exit(1)