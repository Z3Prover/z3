import os
import sys
import shutil
import platform
import subprocess
import multiprocessing
import re
import glob
from setuptools import setup
from distutils.util import get_platform
from distutils.errors import LibError
from distutils.command.build import build as _build
from distutils.command.sdist import sdist as _sdist
from distutils.command.clean import clean as _clean
from setuptools.command.develop import develop as _develop
from setuptools.command.bdist_egg import bdist_egg as _bdist_egg


build_env = dict(os.environ)
build_env['PYTHON'] = sys.executable
build_env['CXXFLAGS'] = build_env.get('CXXFLAGS', '') + " -std=c++11"

# determine where we're building and where sources are
ROOT_DIR = os.path.abspath(os.path.dirname(__file__))
SRC_DIR_LOCAL = os.path.join(ROOT_DIR, 'core')
SRC_DIR_REPO = os.path.join(ROOT_DIR, '..', '..', '..')
SRC_DIR = SRC_DIR_LOCAL if os.path.exists(SRC_DIR_LOCAL) else SRC_DIR_REPO

# determine where binaries are
RELEASE_DIR = os.environ.get('PACKAGE_FROM_RELEASE', None)
if RELEASE_DIR is None:
    BUILD_DIR = os.path.join(SRC_DIR, 'build') # implicit in configure script
    HEADER_DIRS = [os.path.join(SRC_DIR, 'src', 'api'), os.path.join(SRC_DIR, 'src', 'api', 'c++')]
    RELEASE_METADATA = None
    BUILD_PLATFORM = sys.platform
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

# determine where destinations are
LIBS_DIR = os.path.join(ROOT_DIR, 'z3', 'lib')
HEADERS_DIR = os.path.join(ROOT_DIR, 'z3', 'include')
BINS_DIR = os.path.join(ROOT_DIR, 'bin')

# determine platform-specific filenames
if BUILD_PLATFORM in ('darwin', 'osx'):
    LIBRARY_FILE = "libz3.dylib"
    EXECUTABLE_FILE = "z3"
elif BUILD_PLATFORM in ('win32', 'cygwin', 'win'):
    LIBRARY_FILE = "libz3.dll"
    EXECUTABLE_FILE = "z3.exe"
else:
    LIBRARY_FILE = "libz3.so"
    EXECUTABLE_FILE = "z3"

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
    # bail out early if we don't need to do this - it forces a rebuild every time otherwise
    if os.path.exists(BUILD_DIR):
        return
    else:
        os.mkdir(BUILD_DIR)
    # Config options
    cmake_options = {
        # Config Options
        'Z3_SINGLE_THREADED' : False,
        'Z3_BUILD_PYTHON_BINDINGS' : True,
        # Build Options
        'CMAKE_BUILD_TYPE' : 'Release',
        'Z3_BUILD_EXECUTABLE' : True,
        'Z3_BUILD_LIBZ3_SHARED' : True,
        'Z3_LINK_TIME_OPTIMIZATION' : True,
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

    python_dir = None
    if RELEASE_DIR is not None:
        python_dir = os.path.join(RELEASE_DIR, 'bin', 'python')
    elif SRC_DIR == SRC_DIR_LOCAL:
        python_dir = os.path.join(SRC_DIR, 'src', 'api', 'python')
    if python_dir is not None:
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

def _copy_sources():
    """
    Prepare for a source distribution by assembling a minimal set of source files needed
    for building
    """
    shutil.rmtree(SRC_DIR_LOCAL, ignore_errors=True)
    os.mkdir(SRC_DIR_LOCAL)

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

class bdist_egg(_bdist_egg):
    def run(self):
        self.run_command('build')
        _bdist_egg.run(self)

class sdist(_sdist):
    def run(self):
        self.execute(_clean_bins, (), msg="Cleaning binary files and headers")
        self.execute(_copy_sources, (), msg="Copying source files")
        _sdist.run(self)

class clean(_clean):
    def run(self):
        self.execute(_clean_bins, (), msg="Cleaning binary files and headers")
        self.execute(_clean_native_build, (), msg="Cleaning native build")
        _clean.run(self)

# the build directory needs to exist
#try: os.makedirs(os.path.join(ROOT_DIR, 'build'))
#except OSError: pass

if 'bdist_wheel' in sys.argv and '--plat-name' not in sys.argv:
    if RELEASE_DIR is None:
        name = get_platform()
        if 'linux' in name:
            # linux_* platform tags are disallowed because the python ecosystem is fubar
            # linux builds should be built in the centos 5 vm for maximum compatibility
            # see https://github.com/pypa/manylinux
            # see also https://github.com/angr/angr-dev/blob/master/admin/bdist.py
            plat_name = 'manylinux1_' + platform.machine()
        elif 'mingw' in name:
            if platform.architecture()[0] == '64bit':
                plat_name = 'win_amd64'
            else:
                plat_name ='win32'
        else:
            # https://www.python.org/dev/peps/pep-0425/
            plat_name = name.replace('.', '_').replace('-', '_')
    else:
        # extract the architecture of the release from the directory name
        arch = RELEASE_METADATA[1]
        distos = RELEASE_METADATA[2]
        if distos in ('debian', 'ubuntu') or 'linux' in distos:
            raise Exception("Linux binary distributions must be built on centos to conform to PEP 513")
        elif distos == 'glibc':
            if arch == 'x64':
                plat_name = 'manylinux1_x86_64'
            else:
                plat_name = 'manylinux1_i686'
        elif distos == 'win':
            if arch == 'x64':
                plat_name = 'win_amd64'
            else:
                plat_name = 'win32'
        elif distos == 'osx':
            osver = RELEASE_METADATA[3]
            if osver.count('.') > 1:
                osver = '.'.join(osver.split('.')[:2])
            if arch == 'x64':
                plat_name ='macosx_%s_x86_64' % osver.replace('.', '_')
            else:
                raise Exception(f"idk how os {distos} {osver} works. what goes here?")
        else:
            raise Exception(f"idk how to translate between this z3 release os {distos} and the python naming scheme")

    idx = sys.argv.index('bdist_wheel') + 1
    sys.argv.insert(idx, '--plat-name')
    sys.argv.insert(idx + 1, plat_name)
    sys.argv.insert(idx + 2, '--universal')   # supports py2+py3. if --plat-name is not specified this will also mean that the package can be installed on any machine regardless of architecture, so watch out!


setup(
    name='z3-solver',
    version=_z3_version(),
    description='an efficient SMT solver library',
    long_description='Z3 is a theorem prover from Microsoft Research with support for bitvectors, booleans, arrays, floating point numbers, strings, and other data types.\n\nFor documentation, please read http://z3prover.github.io/api/html/z3.html\n\nIn the event of technical difficulties related to configuration, compilation, or installation, please submit issues to https://github.com/angr/angr-z3',
    author="The Z3 Theorem Prover Project",
    maintainer="Audrey Dutcher",
    maintainer_email="audrey@rhelmot.io",
    url='https://github.com/Z3Prover/z3',
    license='MIT License',
    keywords=['z3', 'smt', 'sat', 'prover', 'theorem'],
    packages=['z3'],
    include_package_data=True,
    package_data={
        'z3': [os.path.join('lib', '*'), os.path.join('include', '*.h'), os.path.join('include', 'c++', '*.h')]
    },
    data_files=[('bin',[os.path.join('bin',EXECUTABLE_FILE)])],
    cmdclass={'build': build, 'develop': develop, 'sdist': sdist, 'bdist_egg': bdist_egg, 'clean': clean},
)
