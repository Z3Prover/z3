import os
import sys
import shutil
import platform
import subprocess
import multiprocessing
import re
import glob
from setuptools import setup
from setuptools.command.build import build as _build
from setuptools.command.sdist import sdist as _sdist
from setuptools.command.bdist_wheel import bdist_wheel as _bdist_wheel
from setuptools.command.develop import develop as _develop

class LibError(Exception):
    pass

build_env = dict(os.environ)
build_env['PYTHON'] = sys.executable
build_env['CXXFLAGS'] = build_env.get('CXXFLAGS', '') + " -std=c++20"

# determine where we're building and where sources are
ROOT_DIR = os.path.abspath(os.path.dirname(__file__))
SRC_DIR_LOCAL = os.path.join(ROOT_DIR, 'core')
SRC_DIR_REPO = os.path.join(ROOT_DIR, '..', '..', '..')
SRC_DIR = SRC_DIR_LOCAL if os.path.exists(SRC_DIR_LOCAL) else SRC_DIR_REPO

IS_SINGLE_THREADED = False
ENABLE_LTO = True

IS_PYODIDE = 'PYODIDE_ROOT' in os.environ and os.environ.get('_PYTHON_HOST_PLATFORM', '').startswith('emscripten')


# determine where binaries are
RELEASE_DIR = os.environ.get('PACKAGE_FROM_RELEASE', None)
if RELEASE_DIR is None:
    BUILD_DIR = os.path.join(SRC_DIR, 'build') # implicit in configure script
    HEADER_DIRS = [os.path.join(SRC_DIR, 'src', 'api'), os.path.join(SRC_DIR, 'src', 'api', 'c++')]
    RELEASE_METADATA = None
    if IS_PYODIDE:
        BUILD_PLATFORM = "emscripten"
        BUILD_ARCH = "wasm32"
        BUILD_OS_VERSION = os.environ['_PYTHON_HOST_PLATFORM'].split('_')[1:-1]
        build_env['CFLAGS'] = build_env.get('CFLAGS', '') + " -fexceptions"
        build_env['CXXFLAGS'] = build_env.get('CXXFLAGS', '') + " -fexceptions"
        build_env['LDFLAGS'] = build_env.get('LDFLAGS', '') + " -fexceptions"
        IS_SINGLE_THREADED = True
        ENABLE_LTO = False
        # build with pthread doesn't work. The WASM bindings are also single threaded.
        
    else:
        BUILD_PLATFORM = sys.platform
        BUILD_ARCH = os.environ.get("Z3_CROSS_COMPILING", platform.machine())
        BUILD_OS_VERSION = platform.mac_ver()[0].split(".")[:2]
else:
    if not os.path.isdir(RELEASE_DIR):
        raise Exception("RELEASE_DIR (%s) is not a directory!" % RELEASE_DIR)
    BUILD_DIR = os.path.join(RELEASE_DIR, 'bin')
    HEADER_DIRS = [os.path.join(RELEASE_DIR, 'include')]
    RELEASE_METADATA = os.path.basename(RELEASE_DIR).split('-')
    if RELEASE_METADATA[0] != 'z3' or len(RELEASE_METADATA) not in (4, 5):
        raise Exception("RELEASE_DIR (%s) must be in the format z3-version-arch-os[-osversion] so we can extract metadata from it. Sorry!" % RELEASE_DIR)
    RELEASE_METADATA.pop(0)
    BUILD_PLATFORM = RELEASE_METADATA[2]
    BUILD_ARCH = RELEASE_METADATA[1]
    if len(RELEASE_METADATA) == 4:
        BUILD_OS_VERSION = RELEASE_METADATA[3].split(".")
    else:
        BUILD_OS_VERSION = None

# determine where destinations are
LIBS_DIR = os.path.join(ROOT_DIR, 'z3', 'lib')
HEADERS_DIR = os.path.join(ROOT_DIR, 'z3', 'include')
BINS_DIR = os.path.join(ROOT_DIR, 'bin')

# determine platform-specific filenames

if BUILD_PLATFORM in ('sequoia','darwin', 'osx'):
    LIBRARY_FILE = "libz3.dylib"
    EXECUTABLE_FILE = "z3"
elif BUILD_PLATFORM in ('win32', 'cygwin', 'win'):
    LIBRARY_FILE = "libz3.dll"
    EXECUTABLE_FILE = "z3.exe"
elif BUILD_PLATFORM in ('emscripten',):
    LIBRARY_FILE = "libz3.so"
    EXECUTABLE_FILE = "z3.wasm"
else:
    LIBRARY_FILE = "libz3.so"
    EXECUTABLE_FILE = "z3"

# check if cmake is available, and pull it in via PyPI if necessary
SETUP_REQUIRES = []
if not shutil.which("cmake"):
    SETUP_REQUIRES += ["cmake"]

def rmtree(tree):
    if os.path.exists(tree):
        shutil.rmtree(tree, ignore_errors=False)

def _clean_bins():
    """
    Clean up the binary files and headers that are installed along with the bindings
    """
    rmtree(LIBS_DIR)
    rmtree(BINS_DIR)
    rmtree(HEADERS_DIR)

def _clean_native_build():
    """
    Clean the "build" directory in the z3 native root
    """
    rmtree(BUILD_DIR)

def _z3_version():
    post = os.getenv('Z3_VERSION_SUFFIX', '')
    if RELEASE_DIR is None:
        fn = os.path.join(SRC_DIR, 'scripts', 'mk_project.py')
        if os.path.exists(fn):
            with open(fn) as f:
                for line in f:
                    n = re.match(r".*set_version\((.*), (.*), (.*), (.*)\).*", line)
                    if not n is None:
                        return n.group(1) + '.' + n.group(2) + '.' + n.group(3) + '.' + n.group(4) + post
        return "?.?.?.?"
    else:
        version = RELEASE_METADATA[0]
        if version.count('.') == 2:
            version += '.0'
        return version + post

def _configure_z3():
    global IS_SINGLE_THREADED
    global ENABLE_LTO
    # bail out early if we don't need to do this - it forces a rebuild every time otherwise
    if os.path.exists(BUILD_DIR):
        return
    else:
        os.mkdir(BUILD_DIR)
    # Config options
    cmake_options = {
        # Config Options
        'Z3_SINGLE_THREADED' : IS_SINGLE_THREADED,      # avoid solving features that use threads
        'Z3_POLLING_TIMER' : IS_SINGLE_THREADED,         # avoid using timer threads
        'Z3_BUILD_PYTHON_BINDINGS' : True,
        # Build Options
        'CMAKE_BUILD_TYPE' : 'Release',
        'Z3_BUILD_EXECUTABLE' : True,
        'Z3_BUILD_LIBZ3_SHARED' : True,
        'Z3_LINK_TIME_OPTIMIZATION' : ENABLE_LTO,
        'WARNINGS_AS_ERRORS' : 'SERIOUS_ONLY',
        # Disable Unwanted Options
        'Z3_USE_LIB_GMP' : False, # Is default false in python build
        'Z3_INCLUDE_GIT_HASH' : False, # Can be changed if we bundle the .git as well
        'Z3_INCLUDE_GIT_DESCRIBE' : False,
        'Z3_SAVE_CLANG_OPTIMIZATION_RECORDS' : False,
        'Z3_ENABLE_TRACING_FOR_NON_DEBUG' : False,
        'Z3_ENABLE_EXAMPLE_TARGETS' : False,
        'Z3_ENABLE_CFI' : False,
        'Z3_BUILD_DOCUMENTATION' : False,
        'Z3_BUILD_TEST_EXECUTABLES' : False,
        'Z3_BUILD_DOTNET_BINDINGS' : False,
        'Z3_BUILD_JAVA_BINDINGS' : False
    }
    # Convert cmake options to CLI arguments
    for key, val in cmake_options.items():
        if type(val) is bool:
            cmake_options[key] = str(val).upper()

    # Allow command-line arguments to add and override Z3_ options
    for i in range(len(sys.argv) - 1):
        key = sys.argv[i]
        if key.startswith("Z3_"):
            val = sys.argv[i + 1].upper()
            if val == "TRUE" or val == "FALSE":
                cmake_options[key] = val
                
    cmake_args = [ '-D' + key + '=' + value for key,value in cmake_options.items() ]
    args = [ 'cmake', *cmake_args, SRC_DIR ]
    if subprocess.call(args, env=build_env, cwd=BUILD_DIR) != 0:
        raise LibError("Unable to configure Z3.")

def _build_z3():
    if sys.platform == 'win32':
        if subprocess.call(['nmake'], env=build_env,
                           cwd=BUILD_DIR) != 0:
            raise LibError("Unable to build Z3.")
    else:   # linux and macOS
        if subprocess.call(['make', '-j', str(multiprocessing.cpu_count())],
                env=build_env, cwd=BUILD_DIR) != 0:
            raise LibError("Unable to build Z3.")


def _copy_bins():
    """
    Copy the library and header files into their final destinations
    """
    # STEP 1: If we're performing a build from a copied source tree,
    # copy the generated python files into the package

    _clean_bins()

    py_z3_build_dir = os.path.join(BUILD_DIR, 'python', 'z3')
    root_z3_dir = os.path.join(ROOT_DIR, 'z3')
    shutil.copy(os.path.join(py_z3_build_dir, 'z3core.py'), root_z3_dir)
    shutil.copy(os.path.join(py_z3_build_dir, 'z3consts.py'), root_z3_dir)

    # STEP 2: Copy the shared library, the executable and the headers

    os.mkdir(LIBS_DIR)
    os.mkdir(BINS_DIR)
    os.mkdir(HEADERS_DIR)
    shutil.copy(os.path.join(BUILD_DIR, LIBRARY_FILE), LIBS_DIR)
    shutil.copy(os.path.join(BUILD_DIR, EXECUTABLE_FILE), BINS_DIR)
    path1 = glob.glob(os.path.join(BUILD_DIR, "msvcp*"))
    path2 = glob.glob(os.path.join(BUILD_DIR, "vcomp*"))
    path3 = glob.glob(os.path.join(BUILD_DIR, "vcrun*"))
    for filepath in path1 + path2 + path3:
        shutil.copy(filepath, LIBS_DIR)

    for header_dir in HEADER_DIRS:
        for fname in os.listdir(header_dir):
            if not fname.endswith('.h'):
                continue
            shutil.copy(os.path.join(header_dir, fname), os.path.join(HEADERS_DIR, fname))

    # This hack lets z3 installed libs link on M1 macs; it is a hack, not a proper fix
    # @TODO: Linked issue: https://github.com/Z3Prover/z3/issues/5926
    major_minor = '.'.join(_z3_version().split('.')[:2])
    link_name = None
    if BUILD_PLATFORM in ('win32', 'cygwin', 'win'):
        pass # TODO: When windows VMs work on M1, fill this in
    elif BUILD_PLATFORM in ('sequoia', 'darwin', 'osx'):
        split = LIBRARY_FILE.split('.')
        link_name = split[0] + '.' + major_minor + '.' + split[1]
    else:
        link_name = LIBRARY_FILE + '.' + major_minor
    if link_name:
        os.symlink(LIBRARY_FILE, os.path.join(LIBS_DIR, link_name), True)

def _copy_sources():
    """
    Prepare for a source distribution by assembling a minimal set of source files needed
    for building
    """
    shutil.rmtree(SRC_DIR_LOCAL, ignore_errors=True)
    os.mkdir(SRC_DIR_LOCAL)

#   shutil.copy(os.path.join(SRC_DIR_REPO, 'LICENSE.txt'), ROOT_DIR)
    shutil.copy(os.path.join(SRC_DIR_REPO, 'LICENSE.txt'), SRC_DIR_LOCAL)
    shutil.copy(os.path.join(SRC_DIR_REPO, 'z3.pc.cmake.in'), SRC_DIR_LOCAL)
    shutil.copy(os.path.join(SRC_DIR_REPO, 'CMakeLists.txt'), SRC_DIR_LOCAL)
    shutil.copytree(os.path.join(SRC_DIR_REPO, 'cmake'), os.path.join(SRC_DIR_LOCAL, 'cmake'))
    shutil.copytree(os.path.join(SRC_DIR_REPO, 'scripts'), os.path.join(SRC_DIR_LOCAL, 'scripts'))

    # Copy in src, but avoid recursion
    def ignore_python_setup_files(src, _):
        if os.path.normpath(src).endswith('api/python'):
            return ['core', 'dist', 'MANIFEST', 'MANIFEST.in', 'setup.py', 'z3_solver.egg-info']
        return []
    shutil.copytree(os.path.join(SRC_DIR_REPO, 'src'), os.path.join(SRC_DIR_LOCAL, 'src'),
            ignore=ignore_python_setup_files)

class build(_build):
    def run(self):
        if RELEASE_DIR is None:
            self.execute(_configure_z3, (), msg="Configuring Z3")
            self.execute(_build_z3, (), msg="Building Z3")
        self.execute(_copy_bins, (), msg="Copying binaries")
        _build.run(self)

class develop(_develop):
    def run(self):
        self.execute(_configure_z3, (), msg="Configuring Z3")
        self.execute(_build_z3, (), msg="Building Z3")
        self.execute(_copy_bins, (), msg="Copying binaries")
        _develop.run(self)

class sdist(_sdist):
    def run(self):
        self.execute(_clean_bins, (), msg="Cleaning binary files and headers")
        self.execute(_copy_sources, (), msg="Copying source files")
        _sdist.run(self)

# The Azure Dev Ops pipelines use internal OS version tagging that don't correspond
# to releases.

internal_build_re = re.compile("(.+)\_7")

class bdist_wheel(_bdist_wheel):

    def remove_build_machine_os_version(self, platform, os_version_tag):
        if platform in ["osx", "darwin", "sequoia"]:
            m = internal_build_re.search(os_version_tag)
            if m:
                return m.group(1) + "_0"
        return os_version_tag
            
            
    def finalize_options(self):
        if BUILD_ARCH is not None and BUILD_PLATFORM is not None:
            os_version_tag = '_'.join(BUILD_OS_VERSION) if BUILD_OS_VERSION is not None else 'xxxxxx'
            os_version_tag = self.remove_build_machine_os_version(BUILD_PLATFORM, os_version_tag)
            TAGS = {
                # linux tags cannot be deployed - they must be auditwheel'd to pick the right compatibility tag based on imported libc symbol versions
                ("linux", "x86_64"): "linux_x86_64",
                ("linux", "aarch64"): "linux_aarch64",
                ('linux', "riscv64"): "linux_riscv64",
                # windows arm64 is not supported by pypi yet
                ("win", "x64"): "win_amd64",
                ("win", "x86"): "win32",
                ("osx", "x64"): f"macosx_{os_version_tag}_x86_64",
                ("osx", "arm64"): f"macosx_{os_version_tag}_arm64",
                ("darwin", "x86_64"): f"macosx_{os_version_tag}_x86_64",
                ("darwin", "x64"): f"macosx_{os_version_tag}_x86_64",
                ("darwin", "arm64"): f"macosx_{os_version_tag}_arm64",
                ("sequoia", "x64"): f"macosx_{os_version_tag}_x86_64",
                ("sequoia", "x86_64"): f"macosx_{os_version_tag}_x86_64",
                ("sequoia", "arm64"): f"macosx_{os_version_tag}_arm64",
                ("emscripten", "wasm32"): f"emscripten_{os_version_tag}_wasm32",
            }  # type: dict[tuple[str, str], str]
            self.plat_name = TAGS[(BUILD_PLATFORM, BUILD_ARCH)]
        return super().finalize_options()


setup(
    name='z3-solver',
    version=_z3_version(),
    description='an efficient SMT solver library',
    long_description='Z3 is a theorem prover from Microsoft Research with support for bitvectors, booleans, arrays, floating point numbers, strings, and other data types.\n\nFor documentation, please read http://z3prover.github.io/api/html/z3.html',
    author="The Z3 Theorem Prover Project",
    maintainer="Audrey Dutcher and Nikolaj Bjorner",
    maintainer_email="audrey@rhelmot.io",
    url='https://github.com/Z3Prover/z3',
    license='MIT License',
    keywords=['z3', 'smt', 'sat', 'prover', 'theorem'],
    packages=['z3'],
    setup_requires = SETUP_REQUIRES,
    install_requires = ["importlib-resources; python_version < '3.9'"],
    include_package_data=True,
    package_data={
        'z3': [os.path.join('lib', '*'), os.path.join('include', '*.h'), os.path.join('include', 'c++', '*.h')]
    },
    data_files=[('bin',[os.path.join('bin',EXECUTABLE_FILE)])],
    cmdclass={'build': build, 'develop': develop, 'sdist': sdist, 'bdist_wheel': bdist_wheel},
)
