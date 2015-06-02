import os
import sys
import subprocess
import multiprocessing
from distutils.core import setup
from distutils.errors import LibError
from distutils.command.build import build as _build

build_env = dict(os.environ)
build_env['PYTHON'] = sys.executable

build_dir = os.path.abspath(os.path.dirname(__file__))

class build(_build):
    @staticmethod
    def _configure():
        if subprocess.call([ os.path.join(build_dir, 'configure') ],
                     env=build_env, cwd=build_dir) != 0:
            raise LibError('Unable to configure Z3.')

    @staticmethod
    def _build():
        if subprocess.call(['make', '-C', os.path.join(build_dir, 'build'),
                      '-j', str(multiprocessing.cpu_count())],
                     env=build_env, cwd=build_dir) != 0:
            raise LibError('Unable to build Z3.')

    def run(self):
        self.execute(self._configure, (), msg="Configuring Z3")
        self.execute(self._build, (), msg="Building Z3")

# the build directory needs to exist
try: os.makedirs(os.path.join(build_dir, 'build'))
except OSError: pass

setup(
    name='z3',
    version='4.4',
    description='The Z3 Theorem Prover',
    long_description='Z3 is a theorem prover from Microsoft Research.',
    author="The Z3 Theorem Prover Project",
    maintainer="Yan Shoshitaishvili",
    maintainer_email="yans@yancomm.net",
    url='https://github.com/Z3Prover/z3',
    license='MIT License',
    keywords=['z3', 'smt', 'sat', 'prover', 'theorem'],
    package_dir={'': 'build'},
    packages=[''],
    data_files=[
        ('lib', (os.path.join(build_dir, 'build/libz3.so'),)),
        ('include', tuple(os.path.join(build_dir, f) for f in ('src/api/z3.h',
                     'src/api/z3_v1.h', 'src/api/z3_macros.h',
                     'src/api/z3_api.h', 'src/api/z3_algebraic.h',
                     'src/api/z3_polynomial.h', 'src/api/z3_rcf.h',
                     'src/api/z3_interp.h', 'src/api/z3_fpa.h',
                     'src/api/c++/z3++.h') )),
    ],
    scripts=[ os.path.join(build_dir, 'build/z3') ] if sys.version_info[0] == 2 else [ ],
    cmdclass={'build': build},
)
