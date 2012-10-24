AC_INIT([z3], [4.2])

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
AC_SUBST(PYTHON_PACKAGE_DIR)
AC_SUBST(HAS_PYTHON)
rm -f tst_python.py

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
AC_PROG_CXX(g++)

AC_PROG_MAKE_SET

AC_LANG_CPLUSPLUS

# Sets GREP
AC_PROG_GREP

# Sets SED
AC_PROG_SED

# Sets OPENMP_CFLAGS
AC_OPENMP

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
  SLIBFLAGS="-dynamiclib -fopenmp"
  SLIBEXTRAFLAGS=""
  COMP_VERSIONS="-compatibility_version \$(Z3_VERSION) -current_version \$(Z3_VERSION)"
  STATIC_FLAGS=
], [test "$host_os" = "Linux"], [
  PLATFORM=linux
  SO_EXT=.so
  SLIBFLAGS="-shared -fopenmp -Wl,--whole-archive"
  SLIBEXTRAFLAGS="-Wl,--no-whole-archive"
  COMP_VERSIONS=
  STATIC_FLAGS=-static
], [test "${host_os:0:6}" = "CYGWIN"], [
   PLATFORM=win
   SO_EXT=.dll
   LDFLAGS=
   SLIBFLAGS="-shared -fopenmp"
   SLIBEXTRAFLAGS=""
   COMP_VERSIONS=
   STATIC_FLAGS=-static
   CXXFLAGS+=" -D_CYGWIN"
],
[
  AC_MSG_ERROR([Unknown host platform: $host_os])
])
AC_SUBST(SLIBFLAGS)
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
   CXXFLAGS="-fPIC"
   CPPFLAGS="$CPPFLAGS -D_AMD64_"
   dnl Only enable use of thread local storage for 64-bit Linux. It is disabled for OSX and 32-bit Linux
   if test $PLATFORM = "linux"; then
      CPPFLAGS="$CPPFLAGS -D_USE_THREAD_LOCAL" 
   fi
   EXTRA_LIBS=""
   IS_X64="yes"
else
   CXXFLAGS=""
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

if test "$HAS_PYTHON" = "0"; then 
   if test -d build/Makefile; then
      # Python is not installed, but Makefile was pre generated
      # Just copy configuration and terminate
      cp scripts/config-release.mk build/config.mk
cat <<EOF
Z3 was configured with success.
Host platform:  $PLATFORM
Arithmetic:     $ARITH
Python Support: $HAS_PYTHON_MSG
Python:         $PYTHON 
Prefix:         $prefix
64-bit:         $IS_X64

Type 'cd build; make' to compile Z3.
Type 'sudo make install' to install Z3.
Type 'sudo make install-z3py' to install Z3 Python (Z3Py) bindings.
EOF
   else
      AC_MSG_ERROR([Pre generated Makefiles were not detected. You need python to generate the Z3 Makefiles.\nPlease download python at http://python.org])
   fi
else
   # Python is available, give user the option to generate the make files wherever they want
cat <<EOF
Z3 was configured with success.
Host platform:  $PLATFORM
Arithmetic:     $ARITH
Python Support: $HAS_PYTHON_MSG
Python:         $PYTHON 
Prefix:         $prefix
64-bit:         $IS_X64

Type 'python scripts/mk_make.py' to generate Makefiles in the subdirectory 'build'.
Type 'cd build; make' to make Z3.
Type 'sudo make install' to install Z3.
Type 'sudo make install-z3py' to install Z3 Python (Z3Py) bindings.
EOF

fi



