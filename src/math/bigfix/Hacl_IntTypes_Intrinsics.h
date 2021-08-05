/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#ifndef __Hacl_IntTypes_Intrinsics_H
#define __Hacl_IntTypes_Intrinsics_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "math/bigfix/types.h"
#include "math/bigfix/LowStar_Endianness.h"
#include <string.h>
#include "math/bigfix/target.h"

static inline uint32_t
Hacl_IntTypes_Intrinsics_add_carry_u32(uint32_t cin, uint32_t x, uint32_t y, uint32_t *r)
{
  uint32_t res = x + cin + y;
  uint32_t
  c = (~FStar_UInt32_gte_mask(res, x) | (FStar_UInt32_eq_mask(res, x) & cin)) & (uint32_t)1U;
  r[0U] = res;
  return c;
}

static inline uint64_t
Hacl_IntTypes_Intrinsics_add_carry_u64(uint64_t cin, uint64_t x, uint64_t y, uint64_t *r)
{
  uint64_t res = x + cin + y;
  uint64_t
  c = (~FStar_UInt64_gte_mask(res, x) | (FStar_UInt64_eq_mask(res, x) & cin)) & (uint64_t)1U;
  r[0U] = res;
  return c;
}

static inline uint32_t
Hacl_IntTypes_Intrinsics_sub_borrow_u32(uint32_t cin, uint32_t x, uint32_t y, uint32_t *r)
{
  uint32_t res = x - y - cin;
  uint32_t
  c =
    ((FStar_UInt32_gte_mask(res, x) & ~FStar_UInt32_eq_mask(res, x))
    | (FStar_UInt32_eq_mask(res, x) & cin))
    & (uint32_t)1U;
  r[0U] = res;
  return c;
}

static inline uint64_t
Hacl_IntTypes_Intrinsics_sub_borrow_u64(uint64_t cin, uint64_t x, uint64_t y, uint64_t *r)
{
  uint64_t res = x - y - cin;
  uint64_t
  c =
    ((FStar_UInt64_gte_mask(res, x) & ~FStar_UInt64_eq_mask(res, x))
    | (FStar_UInt64_eq_mask(res, x) & cin))
    & (uint64_t)1U;
  r[0U] = res;
  return c;
}

#if defined(__cplusplus)
}
#endif

#define __Hacl_IntTypes_Intrinsics_H_DEFINED
#endif
