// This is used by the CMake build to detect
// what architecture the compiler is targeting.
// TODO: Add more targets here
#if defined(__i386__) || defined(_M_IX86)
#error CMAKE_TARGET_ARCH_i686
#elif defined(__x86_64__) || defined(_M_X64)
#error CMAKE_TARGET_ARCH_x86_64
#elif defined(__ARM_ARCH_ISA_A64)
#error CMAKE_TARGET_ARCH_arm64
#elif defined(__ARM_ARCH)
#error CMAKE_TARGET_ARCH_arm
#else
#error CMAKE_TARGET_ARCH_unknown
#endif
