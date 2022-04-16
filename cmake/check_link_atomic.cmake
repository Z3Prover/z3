set(ATOMIC_TEST_SOURCE "
#include <atomic>
std::atomic<int> x;
std::atomic<short> y;
std::atomic<char> z;
std::atomic<long long> w;
int main() {
	++z;
	++y;
    ++w;
	return ++x;
}")
CHECK_CXX_SOURCE_COMPILES("${ATOMIC_TEST_SOURCE}" BUILTIN_ATOMIC)
if (NOT BUILTIN_ATOMIC)
  set(CMAKE_REQUIRED_LIBRARIES atomic)
  CHECK_CXX_SOURCE_COMPILES("${ATOMIC_TEST_SOURCE}" ATOMICS_REQUIRE_LIBATOMIC)
  unset(CMAKE_REQUIRED_LIBRARIES)
  if (ATOMICS_REQUIRE_LIBATOMIC)
    list(APPEND Z3_DEPENDENT_LIBS atomic)
  else()
    message(FATAL_ERROR "Host compiler must support std::atomic!")
  endif()
endif()
