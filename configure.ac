AC_INIT([z3], [4.2])
AC_CONFIG_SRCDIR(src/util/util.cpp)
AC_PREFIX_DEFAULT(/usr)

###################
#
# Testing python
#
###################
AC_ARG_WITH(python,
[AS_HELP_STRING([--with-python=PYTHON_PATH],
		[specify the location of the python 2.x executable.])])

PYTHON="python"
if test "x$with_python" != x; then
  PYTHON="$with_python"
fi

AC_SUBST(PYTHON)

cat > tst_python.py <<EOF
from sys import version
if version >= "3":
   exit(1)
exit(0)
EOF

if $PYTHON tst_python.py; then
  HAS_PYTHON="1"
  HAS_PYTHON_MSG="yes"
cat > get_py_dir.py << EOF
import distutils.sysconfig
print distutils.sysconfig.get_python_lib()
EOF
  if $PYTHON get_py_dir.py > dir.txt; then
    PYTHON_PACKAGE_DIR=`cat dir.txt`
  else
    HAS_PYTHON="0"
    HAS_PYTHON_MSG="no"
  fi
  rm -f dir.txt
  rm -f get_py_dir.py
else
  HAS_PYTHON="0"
  HAS_PYTHON_MSG="no"
fi
rm -f tst_python.py

if test "$HAS_PYTHON" = "0"; then 
   AC_MSG_ERROR([You need Python 2.x to generate the Z3 Makefiles.\nPlease download python at http://python.org])
fi

AC_SUBST(PYTHON_PACKAGE_DIR)

###################
#
# Configuring bignum package
#
###################
# Select big num package
ARITH="internal"
AC_ARG_WITH([gmp], [AS_HELP_STRING([--with-gmp], [Use GMP for multi-precision naturals (default=no)])], [use_gmp=yes], [use_gmp=no])
AS_IF([test "$use_gmp" = "yes"],[
  ARITH="gmp"
  CPPFLAGS="$CPPFLAGS -D_MP_GMP"
],[
  CPPFLAGS="$CPPFLAGS -D_MP_INTERNAL"
])
AC_SUBST(EXTRA_LIB_SRCS)

if test "$ARITH" = "gmp"; then
   AC_CHECK_LIB(gmp, __gmpz_init, ,   
                [AC_MSG_ERROR([GNU MP not found, see http://gmplib.org/])])
   AC_CHECK_HEADER([gmp.h], GMP='gmp', AC_MSG_ERROR([GMP include file not found]))
   AC_SUBST(LIBS)
   echo $CPPFLAGS
fi

###################
#
# Basic configuration
#
###################
# Sets CXX
AC_LANG([C++])
AC_PROG_CXX(g++ clang++ false)
AC_PROG_CC
if test $CXX = "false"; then
   AC_MSG_ERROR([C++ compiler was not found])
fi

AC_PROG_MAKE_SET

AC_LANG_CPLUSPLUS

# Sets GREP
AC_PROG_GREP

# Sets SED
AC_PROG_SED

AS_IF([test "$CXX" = "g++"], [
   # Enable OpenMP
   CXXFLAGS+=" -fopenmp"  
   LDFLAGS+=" -fopenmp"
   SLIBEXTRAFLAGS+=" -fopenmp"
   # Use -mfpmath=sse
   CXXFLAGS+=" -mfpmath=sse"
],
      [test "$CXX" = "clang++"], [
   # OpenMP is not supported in clang++
   CXXFLAGS+=" -D _NO_OMP_"  
],
[
  AC_MSG_ERROR([Unsupported compiler: $CXX])
])

AR=ar
AC_SUBST(AR)

###################
#
# Platform characteristics
#
###################
host_os=`uname -s`

AS_IF([test "$host_os" = "Darwin"], [
  PLATFORM=osx
  SO_EXT=.dylib
  SLIBFLAGS+="-dynamiclib"
  COMP_VERSIONS="-compatibility_version \$(Z3_VERSION) -current_version \$(Z3_VERSION)"
  STATIC_FLAGS=
], [test "$host_os" = "Linux"], [
  PLATFORM=linux
  SO_EXT=.so
  LDFLAGS+=" -lrt"
  SLIBFLAGS+=" -shared"
  COMP_VERSIONS=
  STATIC_FLAGS=-static
  CXXFLAGS+=" -fno-strict-aliasing"
  if test "$CXX" = "clang++"; then
     # More flags for clang++ for Linux
     CXXFLAGS+=" -Wno-unknown-pragmas -Wno-overloaded-virtual -Wno-unused-value"
  fi
  SLIBEXTRAFLAGS+=" -lrt"
], [test "${host_os:0:6}" = "CYGWIN"], [
   PLATFORM=win
   SO_EXT=.dll
   SLIBFLAGS+="-shared"
   COMP_VERSIONS=
   CXXFLAGS+=" -D_CYGWIN -fno-strict-aliasing"
],
[
  AC_MSG_ERROR([Unknown host platform: $host_os])
])

AC_SUBST(SLIBFLAGS)
AC_SUBST(LDFLAGS)
AC_SUBST(SLIBEXTRAFLAGS)
AC_SUBST(SO_EXT)

###################
#
# Checking if 32 or 64 bits
#
###################
AC_CHECK_SIZEOF(int *) 

if test $ac_cv_sizeof_int_p -eq 8; then
   dnl In 64-bit systems we have to compile using -fPIC
   CXXFLAGS+=" -fPIC"
   CPPFLAGS+=" -D_AMD64_"
   dnl Only enable use of thread local storage for 64-bit Linux. It is disabled for OSX and 32-bit Linux
   if test $PLATFORM = "linux"; then
      CPPFLAGS+=" -D_USE_THREAD_LOCAL" 
   fi
   IS_X64="yes"
else
   IS_X64="no"
fi

###################
#
# Generating configuration
#
###################
AC_OUTPUT(scripts/config-debug.mk scripts/config-release.mk)

###################
#
# Checking how to build Z3
#
###################

# Python is available, give user the option to generate the make files wherever they want
cat <<EOF
Z3 was configured with success.
Host platform:  $PLATFORM
Compiler:       $CXX
Arithmetic:     $ARITH
Python:         $PYTHON 
Prefix:         $prefix
64-bit:         $IS_X64

To build and install Z3, execute:
   python scripts/mk_make.py
   cd build
   make
   sudo make install
EOF



