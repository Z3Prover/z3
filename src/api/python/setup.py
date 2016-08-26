import os
import sys
import platform
import subprocess
import multiprocessing
from setuptools import setup
from distutils.errors import LibError
from distutils.command.build import build as _build
from setuptools.command.develop import develop as _develop


build_env = dict(os.environ)
build_env['PYTHON'] = sys.executable
build_env['CXXFLAGS'] = "-std=c++11"

build_dir = os.path.abspath(os.path.dirname(__file__))

if sys.platform == 'darwin':
    library_file = "libz3.dylib"
elif sys.platform == 'win32':
    library_file = "libz3.dll"
else:
    library_file = "libz3.so"

def _configure_z3():
    if sys.platform == 'win32':
        args = [sys.executable, os.path.join(build_dir, 'scripts',
                                             'mk_make.py')]
        if platform.architecture()[0] == '64bit':
            args += ['-x']

        if subprocess.call(args, env=build_env, cwd=build_dir) != 0:
            raise LibError("Unable to configure Z3.")
    else:   # linux and osx
        if subprocess.call([os.path.join(build_dir, 'configure')],
                    env=build_env, cwd=build_dir) != 0:
            raise LibError("Unable to configure Z3.")

def _build_z3():
    if sys.platform == 'win32':
        if subprocess.call(['nmake'], env=build_env,
                           cwd=os.path.join(build_dir, 'build')) != 0:
            raise LibError("Unable to build Z3.")
    else:   # linux and osx
        if subprocess.call(['make', '-C', os.path.join(build_dir, 'build'),
                            '-j', str(multiprocessing.cpu_count())],
                    env=build_env, cwd=build_dir) != 0:
            raise LibError("Unable to build Z3.")

class build(_build):
    def run(self):
        self.execute(_configure_z3, (), msg="Configuring Z3")
        self.execute(_build_z3, (), msg="Building Z3")

class develop(_develop):
    def run(self):
        self.execute(_configure_z3, (), msg="Configuring Z3")
        self.execute(_build_z3, (), msg="Building Z3")

# the build directory needs to exist
try: os.makedirs(os.path.join(build_dir, 'build'))
except OSError: pass

setup(
    name='angr-only-z3-custom',
    version='4.4.1.post4',
    description='pip installable distribution of The Z3 Theorem Prover, for use with angr. Please send all support requests to angr@lists.cs.ucsb.edu!',
    long_description='Z3 is a theorem prover from Microsoft Research. This version is slightly modified by the angr project to enable installation via pip, making it unsupportable by the Z3 project. Please direct all support requests to angr@lists.cs.ucsb.edu!',
    author="The Z3 Theorem Prover Project",
    maintainer="Yan Shoshitaishvili",
    maintainer_email="yans@yancomm.net",
    url='https://github.com/angr/angr-z3',
    license='MIT License',
    keywords=['z3', 'smt', 'sat', 'prover', 'theorem'],
    package_dir={'': 'build'},
    packages=[''],
    data_files=[
        ('lib', (os.path.join(build_dir, 'build', library_file),)),
        ('include', tuple(os.path.join(build_dir, f) for f in ('src/api/z3.h',
                     'src/api/z3_v1.h', 'src/api/z3_macros.h',
                     'src/api/z3_api.h', 'src/api/z3_algebraic.h',
                     'src/api/z3_polynomial.h', 'src/api/z3_rcf.h',
                     'src/api/z3_interp.h', 'src/api/z3_fpa.h',
                     'src/api/c++/z3++.h') )),
    ],
    #scripts=[os.path.join(build_dir, 'build', 'z3')] if sys.version_info[0] == 2 else [],
    cmdclass={'build': build, 'develop': develop},
)
