import os
import subprocess
import multiprocessing
from distutils.core import setup
from distutils.errors import LibError
from distutils.command.build import build as _build

class build(_build):
    @staticmethod
    def _configure():
        if subprocess.call(['./configure']) != 0:
            raise LibError('Unable to configure Z3.')

    @staticmethod
    def _build():
        if subprocess.call(['make', '-C', 'build', '-j',
                      str(multiprocessing.cpu_count())]) != 0:
            raise LibError('Unable to build Z3.')

    def run(self):
        self.execute(self._configure, (), msg="Configuring Z3")
        self.execute(self._build, (), msg="Building Z3")

# the build directory needs to exist
try: os.makedirs(os.path.join(os.path.dirname(__file__), 'build'))
except OSError: pass

setup(
    name='z3',
    version='4.4',
    description='The Z3 Theorem Prover',
    long_description='Z3 is a theorem prover from Microsoft Research.',
    url='https://github.com/Z3Prover/z3',
    license='MIT License',
    keywords=['z3', 'smt', 'sat', 'prover', 'theorem'],
    package_dir={'': 'build'},
    packages=[''],
    data_files=[
        ('lib', ('build/libz3.so',)),
        ('include', ('src/api/z3.h', 'src/api/z3_v1.h', 'src/api/z3_macros.h',
                     'src/api/z3_api.h', 'src/api/z3_algebraic.h',
                     'src/api/z3_polynomial.h', 'src/api/z3_rcf.h',
                     'src/api/z3_interp.h', 'src/api/z3_fpa.h',
                     'src/api/c++/z3++.h')),
    ],
    scripts=['build/z3'],
    cmdclass={'build': build},
)
