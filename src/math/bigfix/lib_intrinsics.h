#pragma once

#include <sys/types.h>

#if __has_include("config.h")
#include "config.h"
#endif

#if defined(COMPILE_INTRINSICS)
#if defined(_MSC_VER)
#include <immintrin.h>
#else
#include <x86intrin.h>
#endif
#endif

#if !defined(COMPILE_INTRINSICS)

#include "Hacl_IntTypes_Intrinsics.h"

#define Lib_IntTypes_Intrinsics_add_carry_u32(x1, x2, x3, x4) \
  (Hacl_IntTypes_Intrinsics_add_carry_u32(x1, x2, x3, x4))

#define Lib_IntTypes_Intrinsics_add_carry_u64(x1, x2, x3, x4) \
  (Hacl_IntTypes_Intrinsics_add_carry_u64(x1, x2, x3, x4))

#define Lib_IntTypes_Intrinsics_sub_borrow_u32(x1, x2, x3, x4) \
  (Hacl_IntTypes_Intrinsics_sub_borrow_u32(x1, x2, x3, x4))

#define Lib_IntTypes_Intrinsics_sub_borrow_u64(x1, x2, x3, x4) \
  (Hacl_IntTypes_Intrinsics_sub_borrow_u64(x1, x2, x3, x4))

#else

#define Lib_IntTypes_Intrinsics_add_carry_u32(x1, x2, x3, x4) \
  (_addcarry_u32(x1, x2, x3, (unsigned int *) x4))

#define Lib_IntTypes_Intrinsics_add_carry_u64(x1, x2, x3, x4) \
  (_addcarry_u64(x1, x2, x3, (long long unsigned int *) x4))


/*
   GCC versions prior to 7.2 pass arguments to _subborrow_u{32,64}
   in an incorrect order.

   See https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
*/
#if defined(__GNUC__) && !defined (__clang__) && \
  (__GNUC__ < 7 || (__GNUC__ == 7 && (__GNUC_MINOR__ < 2)))

#define Lib_IntTypes_Intrinsics_sub_borrow_u32(x1, x2, x3, x4) \
  (_subborrow_u32(x1, x3, x2, (unsigned int *) x4))

#define Lib_IntTypes_Intrinsics_sub_borrow_u64(x1, x2, x3, x4) \
  (_subborrow_u64(x1, x3, x2, (long long unsigned int *) x4))

#else

#define Lib_IntTypes_Intrinsics_sub_borrow_u32(x1, x2, x3, x4)  \
  (_subborrow_u32(x1, x2, x3, (unsigned int *) x4))

#define Lib_IntTypes_Intrinsics_sub_borrow_u64(x1, x2, x3, x4)  \
  (_subborrow_u64(x1, x2, x3, (long long unsigned int *) x4))

#endif // GCC < 7.2

#endif // !COMPILE_INTRINSICS
