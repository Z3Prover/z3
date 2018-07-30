import os
import sys
import shutil
import platform
import subprocess
import multiprocessing
import re
from setuptools import setup
from distutils.util import get_platform
from distutils.errors import LibError
from distutils.command.build import build as _build
from distutils.command.sdist import sdist as _sdist
from setuptools.command.develop import develop as _develop
from setuptools.command.bdist_egg import bdist_egg as _bdist_egg


build_env = dict(os.environ)
build_env['PYTHON'] = sys.executable
build_env['CXXFLAGS'] = "-std=c++11"

ROOT_DIR = os.path.abspath(os.path.dirname(__file__))
SRC_DIR_LOCAL = os.path.join(ROOT_DIR, 'core')
SRC_DIR_REPO = os.path.join(ROOT_DIR, '..', '..', '..')
SRC_DIR = SRC_DIR_LOCAL if os.path.exists(SRC_DIR_LOCAL) else SRC_DIR_REPO
BUILD_DIR = os.path.join(SRC_DIR, 'build') # implicit in configure script
LIBS_DIR = os.path.join(ROOT_DIR, 'z3', 'lib')
HEADERS_DIR = os.path.join(ROOT_DIR, 'z3', 'include')
BINS_DIR = os.path.join(ROOT_DIR, 'bin')

if sys.platform == 'darwin':
    LIBRARY_FILE = "libz3.dylib"
    EXECUTABLE_FILE = "z3"
elif sys.platform in ('win32', 'cygwin'):
    LIBRARY_FILE = "libz3.dll"
    EXECUTABLE_FILE = "z3.exe"
else:
    LIBRARY_FILE = "libz3.so"
    EXECUTABLE_FILE = "z3"

def _clean_bins():
    """
    Clean up the binary files and headers that are installed along with the bindings
    """
    shutil.rmtree(LIBS_DIR, ignore_errors=True)
    shutil.rmtree(BINS_DIR, ignore_errors=True)
    shutil.rmtree(HEADERS_DIR, ignore_errors=True)

def _z3_version():
    post = os.getenv('Z3_VERSION_SUFFIX', '')
    fn = os.path.join(SRC_DIR, 'scripts', 'mk_project.py')
    if os.path.exists(fn):
        with open(fn) as f:
            for line in f:
                n = re.match(".*set_version\((.*), (.*), (.*), (.*)\).*", line)
                if not n is None:
                    return n.group(1) + '.' + n.group(2) + '.' + n.group(3) + '.' + n.group(4) + post
    return "?.?.?.?"

def _configure_z3():
    # bail out early if we don't need to do this - it forces a rebuild every time otherwise
    if os.path.exists(BUILD_DIR):
        return
    args = [sys.executable, os.path.join(SRC_DIR, 'scripts', 'mk_make.py')]

    if sys.platform == 'win32' and platform.architecture()[0] == '64bit':
        args += ['-x']

    if subprocess.call(args, env=build_env, cwd=SRC_DIR) != 0:
        raise LibError("Unable to configure Z3.")

def _build_z3():
    if sys.platform == 'win32':
        if subprocess.call(['nmake'], env=build_env,
                           cwd=BUILD_DIR) != 0:
            raise LibError("Unable to build Z3.")
    else:   # linux and osx
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

    if SRC_DIR == SRC_DIR_LOCAL:
        shutil.copy(os.path.join(SRC_DIR, 'src', 'api', 'python', 'z3', 'z3core.py'), os.path.join(ROOT_DIR, 'z3'))
        shutil.copy(os.path.join(SRC_DIR, 'src', 'api', 'python', 'z3', 'z3consts.py'), os.path.join(ROOT_DIR, 'z3'))

    # STEP 2: Copy the shared library, the executable and the headers

    os.mkdir(LIBS_DIR)
    os.mkdir(BINS_DIR)
    os.mkdir(HEADERS_DIR)
    os.mkdir(os.path.join(HEADERS_DIR, 'c++'))
    shutil.copy(os.path.join(BUILD_DIR, LIBRARY_FILE), LIBS_DIR)
    shutil.copy(os.path.join(BUILD_DIR, EXECUTABLE_FILE), BINS_DIR)

    header_files = [x for x in os.listdir(os.path.join(SRC_DIR, 'src', 'api')) if x.endswith('.h')]
    header_files += [os.path.join('c++', x) for x in os.listdir(os.path.join(SRC_DIR, 'src', 'api', 'c++')) if x.endswith('.h')]
    for fname in header_files:
        shutil.copy(os.path.join(SRC_DIR, 'src', 'api', fname), os.path.join(HEADERS_DIR, fname))

def _copy_sources():
    """
    Prepare for a source distribution by assembling a minimal set of source files needed
    for building
    """
    shutil.rmtree(SRC_DIR_LOCAL, ignore_errors=True)
    os.mkdir(SRC_DIR_LOCAL)

    shutil.copy(os.path.join(SRC_DIR_REPO, 'LICENSE.txt'), SRC_DIR_LOCAL)
    shutil.copytree(os.path.join(SRC_DIR_REPO, 'scripts'), os.path.join(SRC_DIR_LOCAL, 'scripts'))
    shutil.copytree(os.path.join(SRC_DIR_REPO, 'examples'), os.path.join(SRC_DIR_LOCAL, 'examples'))
    shutil.copytree(os.path.join(SRC_DIR_REPO, 'src'), os.path.join(SRC_DIR_LOCAL, 'src'),
            ignore=lambda src, names: ['python'] if 'api' in src else [])

    # stub python dir to make build happy
    os.mkdir(os.path.join(SRC_DIR_LOCAL, 'src', 'api', 'python'))
    os.mkdir(os.path.join(SRC_DIR_LOCAL, 'src', 'api', 'python', 'z3'))
    open(os.path.join(SRC_DIR_LOCAL, 'src', 'api', 'python', 'z3', '.placeholder'), 'w').close()
    open(os.path.join(SRC_DIR_LOCAL, 'src', 'api', 'python', 'z3test.py'), 'w').close()

class build(_build):
    def run(self):
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
        self.execute(_clean_bins, (), msg="Cleaning binary files")
        self.execute(_copy_sources, (), msg="Copying source files")
        _sdist.run(self)

# the build directory needs to exist
#try: os.makedirs(os.path.join(ROOT_DIR, 'build'))
#except OSError: pass

if 'bdist_wheel' in sys.argv and '--plat-name' not in sys.argv:
    idx = sys.argv.index('bdist_wheel') + 1
    sys.argv.insert(idx, '--plat-name')
    name = get_platform()
    if 'linux' in name:
        # linux_* platform tags are disallowed because the python ecosystem is fubar
        # linux builds should be built in the centos 5 vm for maximum compatibility
        # see https://github.com/pypa/manylinux
        # see also https://github.com/angr/angr-dev/blob/master/admin/bdist.py
        sys.argv.insert(idx + 1, 'manylinux1_' + platform.machine())
    elif 'mingw' in name:
        if platform.architecture()[0] == '64bit':
            sys.argv.insert(idx + 1, 'win_amd64')
        else:
            sys.argv.insert(idx + 1, 'win32')
    else:
        # https://www.python.org/dev/peps/pep-0425/
        sys.argv.insert(idx + 1, name.replace('.', '_').replace('-', '_'))


setup(
    name='z3-solver',
    version=_z3_version(),
    description='an efficient SMT solver library',
    long_description='Z3 is a theorem prover from Microsoft Research with support for bitvectors, booleans, arrays, floating point numbers, strings, and other data types.\n\nFor documentation, please read http://z3prover.github.io/api/html/z3.html\n\nIn the event of technical difficulties related to configuration, compiliation, or installation, please submit issues to https://github.com/angr/angr-z3',
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
    cmdclass={'build': build, 'develop': develop, 'sdist': sdist, 'bdist_egg': bdist_egg},
)
