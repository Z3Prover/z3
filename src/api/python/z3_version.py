"""
Version detection for z3-solver package.
"""
import os
import re

def get_version():
    """Get the z3 version from the source tree."""
    post = os.getenv('Z3_VERSION_SUFFIX', '')
    
    # Determine where the source directory is located
    ROOT_DIR = os.path.abspath(os.path.dirname(__file__))
    SRC_DIR_LOCAL = os.path.join(ROOT_DIR, 'core')
    SRC_DIR_REPO = os.path.join(ROOT_DIR, '..', '..', '..')
    SRC_DIR = SRC_DIR_LOCAL if os.path.exists(SRC_DIR_LOCAL) else SRC_DIR_REPO
    
    # Check if we're using a release directory
    RELEASE_DIR = os.environ.get('PACKAGE_FROM_RELEASE', None)
    
    if RELEASE_DIR is None:
        fn = os.path.join(SRC_DIR, 'scripts', 'mk_project.py')
        if os.path.exists(fn):
            with open(fn) as f:
                for line in f:
                    n = re.match(r".*set_version\((.*), (.*), (.*), (.*)\).*", line)
                    if not n is None:
                        return n.group(1) + '.' + n.group(2) + '.' + n.group(3) + '.' + n.group(4) + post
        return "4.15.3.0" + post  # fallback version
    else:
        RELEASE_METADATA = os.path.basename(RELEASE_DIR).split('-')
        if RELEASE_METADATA[0] == 'z3' and len(RELEASE_METADATA) >= 4:
            RELEASE_METADATA.pop(0)
            version = RELEASE_METADATA[0]
            if version.count('.') == 2:
                version += '.0'
            return version + post
        return "4.15.3.0" + post  # fallback version

# Make version available at module level
__version__ = get_version()