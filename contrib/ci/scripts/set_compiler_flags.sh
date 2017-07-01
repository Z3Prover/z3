# This script should is intended to be included by other
# scripts and should not be executed directly

: ${TARGET_ARCH?"TARGET_ARCH must be specified"}
: ${ASAN_BUILD?"ASAN_BUILD must be specified"}
: ${UBSAN_BUILD?"UBSAN_BUILD must be specified"}
: ${CC?"CC must be specified"}
: ${CXX?"CXX must be specified"}

case ${TARGET_ARCH} in
  x86_64)
    CXXFLAGS="${CXXFLAGS} -m64"
    CFLAGS="${CFLAGS} -m64"
    ;;
  i686)
    CXXFLAGS="${CXXFLAGS} -m32"
    CFLAGS="${CFLAGS} -m32"
    ;;
  *)
    echo "Unknown arch \"${TARGET_ARCH}\""
    exit 1
esac

if [ "X${ASAN_BUILD}" = "X1" ]; then
  CXXFLAGS="${CXXFLAGS} -fsanitize=address -fno-omit-frame-pointer"
  CFLAGS="${CFLAGS} -fsanitize=address -fno-omit-frame-pointer"
fi

if [ "X${UBSAN_BUILD}" = "X1" ]; then
  CXXFLAGS="${CXXFLAGS} -fsanitize=undefined"
  CFLAGS="${CFLAGS} -fsanitize=undefined"
fi

# Report flags
echo "CXXFLAGS: ${CXXFLAGS}"
echo "CFLAGS: ${CFLAGS}"

# Report compiler
echo "CC: ${CC}"
${CC} --version
echo "CXX: ${CXX}"
${CXX} --version

# Export the values
export CFLAGS
export CXXFLAGS
