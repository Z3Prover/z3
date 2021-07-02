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


#include "math/bigfix/Hacl_Bignum256.h"

/*******************************************************************************

A verified 256-bit bignum library.

This is a 64-bit optimized version, where bignums are represented as an array
of four unsigned 64-bit integers, i.e. uint64_t[4]. Furthermore, the
limbs are stored in little-endian format, i.e. the least significant limb is at
index 0. Each limb is stored in native format in memory. Example:

  uint64_t sixteen[4] = { 0x10; 0x00; 0x00; 0x00 }

We strongly encourage users to go through the conversion functions, e.g.
bn_from_bytes_be, to i) not depend on internal representation choices and ii)
have the ability to switch easily to a 32-bit optimized version in the future.

*******************************************************************************/

/************************/
/* Arithmetic functions */
/************************/


/*
Write `a + b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint64_t[4]
*/
uint64_t Hacl_Bignum256_add(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    uint64_t *res_i0 = res + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, res_i0);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, res_i1);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, res_i2);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, res_i);
  }
  return c;
}

/*
Write `a - b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint64_t[4]
*/
uint64_t Hacl_Bignum256_sub(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    uint64_t *res_i0 = res + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  return c;
}

static inline void add_mod_n(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    uint64_t *res_i0 = res + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res_i0);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res_i1);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res_i2);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res_i);
  }
  uint64_t c00 = c0;
  uint64_t tmp[4U] = { 0U };
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint64_t t1 = res[(uint32_t)4U * i];
    uint64_t t20 = n[(uint32_t)4U * i];
    uint64_t *res_i0 = tmp + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tmp + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tmp + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tmp + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    uint64_t *res_i = tmp + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t c1 = c;
  uint64_t c2 = c00 - c1;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

/*
Write `a * b` in `res`.

  The arguments a and b are meant to be 256-bit bignums, i.e. uint64_t[4].
  The outparam res is meant to be a 512-bit bignum, i.e. uint64_t[8].
*/
void Hacl_Bignum256_mul(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint32_t resLen = (uint32_t)8U;
  memset(res, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    uint64_t bj = b[i0];
    uint64_t *res_j = res + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
    {
      uint64_t a_i = a[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
      uint64_t a_i0 = a[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
      uint64_t a_i1 = a[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
      uint64_t a_i2 = a[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
    }
    for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
    {
      uint64_t a_i = a[i];
      uint64_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i);
    }
    uint64_t r = c;
    res[(uint32_t)4U + i0] = r;
  }
}

/*
Write `a * a` in `res`.

  The argument a is meant to be a 256-bit bignum, i.e. uint64_t[4].
  The outparam res is meant to be a 512-bit bignum, i.e. uint64_t[8].
*/
void Hacl_Bignum256_sqr(uint64_t *a, uint64_t *res)
{
  uint32_t resLen = (uint32_t)8U;
  memset(res, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    uint64_t *ab = a;
    uint64_t a_j = a[i0];
    uint64_t *res_j = res + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < i0 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t a_i = ab[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i0);
      uint64_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, a_j, c, res_i1);
      uint64_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, a_j, c, res_i2);
      uint64_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = i0 / (uint32_t)4U * (uint32_t)4U; i < i0; i++)
    {
      uint64_t a_i = ab[i];
      uint64_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i);
    }
    uint64_t r = c;
    res[i0 + i0] = r;
  }
  uint64_t c0 = Hacl_Bignum_Addition_bn_add_eq_len_u64(resLen, res, res, res);
  KRML_CHECK_SIZE(sizeof (uint64_t), resLen);
  uint64_t *tmp = alloca(resLen * sizeof (uint64_t));
  memset(tmp, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    FStar_UInt128_uint128 res1 = FStar_UInt128_mul_wide(a[i], a[i]);
    uint64_t hi = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
    uint64_t lo = FStar_UInt128_uint128_to_uint64(res1);
    tmp[(uint32_t)2U * i] = lo;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;
  }
  uint64_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u64(resLen, res, tmp, res);
}

static inline void precompr2(uint32_t nBits, uint64_t *n, uint64_t *res)
{
  memset(res, 0U, (uint32_t)4U * sizeof (uint64_t));
  uint32_t i = nBits / (uint32_t)64U;
  uint32_t j = nBits % (uint32_t)64U;
  res[i] = res[i] | (uint64_t)1U << j;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)512U - nBits; i0++)
  {
    add_mod_n(n, res, res, res);
  }
}

static inline void reduction(uint64_t *n, uint64_t nInv, uint64_t *c, uint64_t *res)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    uint64_t qj = nInv * c[i0];
    uint64_t *res_j0 = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
    {
      uint64_t a_i = n[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j0 + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i0);
      uint64_t a_i0 = n[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j0 + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c1, res_i1);
      uint64_t a_i1 = n[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j0 + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c1, res_i2);
      uint64_t a_i2 = n[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j0 + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c1, res_i);
    }
    for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
    {
      uint64_t a_i = n[i];
      uint64_t *res_i = res_j0 + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i);
    }
    uint64_t r = c1;
    uint64_t c10 = r;
    uint64_t *resb = c + (uint32_t)4U + i0;
    uint64_t res_j = c[(uint32_t)4U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c10, res_j, resb);
  }
  memcpy(res, c + (uint32_t)4U, (uint32_t)4U * sizeof (uint64_t));
  uint64_t c00 = c0;
  uint64_t tmp[4U] = { 0U };
  uint64_t c1 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint64_t t1 = res[(uint32_t)4U * i];
    uint64_t t20 = n[(uint32_t)4U * i];
    uint64_t *res_i0 = tmp + (uint32_t)4U * i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, res_i0);
    uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tmp + (uint32_t)4U * i + (uint32_t)1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t21, res_i1);
    uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tmp + (uint32_t)4U * i + (uint32_t)2U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t22, res_i2);
    uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tmp + (uint32_t)4U * i + (uint32_t)3U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    uint64_t *res_i = tmp + i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, res_i);
  }
  uint64_t c10 = c1;
  uint64_t c2 = c00 - c10;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

static inline void areduction(uint64_t *n, uint64_t nInv, uint64_t *c, uint64_t *res)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    uint64_t qj = nInv * c[i0];
    uint64_t *res_j0 = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
    {
      uint64_t a_i = n[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j0 + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i0);
      uint64_t a_i0 = n[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j0 + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c1, res_i1);
      uint64_t a_i1 = n[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j0 + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c1, res_i2);
      uint64_t a_i2 = n[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j0 + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c1, res_i);
    }
    for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
    {
      uint64_t a_i = n[i];
      uint64_t *res_i = res_j0 + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i);
    }
    uint64_t r = c1;
    uint64_t c10 = r;
    uint64_t *resb = c + (uint32_t)4U + i0;
    uint64_t res_j = c[(uint32_t)4U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c10, res_j, resb);
  }
  memcpy(res, c + (uint32_t)4U, (uint32_t)4U * sizeof (uint64_t));
  uint64_t c00 = c0;
  uint64_t tmp[4U] = { 0U };
  uint64_t c1 = Hacl_Bignum256_sub(res, n, tmp);
  uint64_t m = (uint64_t)0U - c00;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (m & tmp[i]) | (~m & res[i]);
    os[i] = x;
  }
}

static inline void
amont_mul(uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *bM, uint64_t *resM)
{
  uint64_t c[8U] = { 0U };
  uint32_t resLen = (uint32_t)8U;
  memset(c, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    uint64_t bj = bM[i0];
    uint64_t *res_j = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
    {
      uint64_t a_i = aM[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c1, res_i0);
      uint64_t a_i0 = aM[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c1, res_i1);
      uint64_t a_i1 = aM[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c1, res_i2);
      uint64_t a_i2 = aM[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c1, res_i);
    }
    for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
    {
      uint64_t a_i = aM[i];
      uint64_t *res_i = res_j + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c1, res_i);
    }
    uint64_t r = c1;
    c[(uint32_t)4U + i0] = r;
  }
  areduction(n, nInv_u64, c, resM);
}

static inline void amont_sqr(uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *resM)
{
  uint64_t c[8U] = { 0U };
  uint32_t resLen = (uint32_t)8U;
  memset(c, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    uint64_t *ab = aM;
    uint64_t a_j = aM[i0];
    uint64_t *res_j = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < i0 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t a_i = ab[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c1, res_i0);
      uint64_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, a_j, c1, res_i1);
      uint64_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, a_j, c1, res_i2);
      uint64_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, a_j, c1, res_i);
    }
    for (uint32_t i = i0 / (uint32_t)4U * (uint32_t)4U; i < i0; i++)
    {
      uint64_t a_i = ab[i];
      uint64_t *res_i = res_j + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c1, res_i);
    }
    uint64_t r = c1;
    c[i0 + i0] = r;
  }
  uint64_t c0 = Hacl_Bignum_Addition_bn_add_eq_len_u64(resLen, c, c, c);
  KRML_CHECK_SIZE(sizeof (uint64_t), resLen);
  uint64_t *tmp = alloca(resLen * sizeof (uint64_t));
  memset(tmp, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    FStar_UInt128_uint128 res = FStar_UInt128_mul_wide(aM[i], aM[i]);
    uint64_t hi = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res, (uint32_t)64U));
    uint64_t lo = FStar_UInt128_uint128_to_uint64(res);
    tmp[(uint32_t)2U * i] = lo;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;
  }
  uint64_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u64(resLen, c, tmp, c);
  areduction(n, nInv_u64, c, resM);
}

static inline void
bn_slow_precomp(uint64_t *n, uint64_t mu, uint64_t *r2, uint64_t *a, uint64_t *res)
{
  uint64_t a_mod[4U] = { 0U };
  uint64_t a1[8U] = { 0U };
  memcpy(a1, a, (uint32_t)8U * sizeof (uint64_t));
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    uint64_t qj = mu * a1[i0];
    uint64_t *res_j0 = a1 + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
    {
      uint64_t a_i = n[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j0 + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c, res_i0);
      uint64_t a_i0 = n[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j0 + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c, res_i1);
      uint64_t a_i1 = n[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j0 + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c, res_i2);
      uint64_t a_i2 = n[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j0 + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c, res_i);
    }
    for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
    {
      uint64_t a_i = n[i];
      uint64_t *res_i = res_j0 + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c, res_i);
    }
    uint64_t r = c;
    uint64_t c1 = r;
    uint64_t *resb = a1 + (uint32_t)4U + i0;
    uint64_t res_j = a1[(uint32_t)4U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c1, res_j, resb);
  }
  memcpy(a_mod, a1 + (uint32_t)4U, (uint32_t)4U * sizeof (uint64_t));
  uint64_t c00 = c0;
  uint64_t tmp[4U] = { 0U };
  uint64_t c1 = Hacl_Bignum256_sub(a_mod, n, tmp);
  uint64_t m = (uint64_t)0U - c00;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = a_mod;
    uint64_t x = (m & tmp[i]) | (~m & a_mod[i]);
    os[i] = x;
  }
  uint64_t c[8U] = { 0U };
  Hacl_Bignum256_mul(a_mod, r2, c);
  reduction(n, mu, c, res);
}

/*
Write `a mod n` in `res`.

  The argument a is meant to be a 512-bit bignum, i.e. uint64_t[8].
  The argument n and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • 1 < n
   • n % 2 = 1 
*/
bool Hacl_Bignum256_mod(uint64_t *n, uint64_t *a, uint64_t *res)
{
  uint64_t one[4U] = { 0U };
  memset(one, 0U, (uint32_t)4U * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint64_t bit0 = n[0U] & (uint64_t)1U;
  uint64_t m0 = (uint64_t)0U - bit0;
  uint64_t acc = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(one[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(one[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t m1 = acc;
  uint64_t is_valid_m = m0 & m1;
  uint32_t
  nBits = (uint32_t)64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64((uint32_t)4U, n);
  if (is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU)
  {
    uint64_t r2[4U] = { 0U };
    precompr2(nBits, n, r2);
    uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
    bn_slow_precomp(n, mu, r2, a, res);
  }
  else
  {
    memset(res, 0U, (uint32_t)4U * sizeof (uint64_t));
  }
  return is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}

static uint64_t exp_check(uint64_t *n, uint64_t *a, uint32_t bBits, uint64_t *b)
{
  uint64_t one[4U] = { 0U };
  memset(one, 0U, (uint32_t)4U * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint64_t bit0 = n[0U] & (uint64_t)1U;
  uint64_t m0 = (uint64_t)0U - bit0;
  uint64_t acc0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(one[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(one[i], n[i]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t m10 = acc0;
  uint64_t m00 = m0 & m10;
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  }
  uint64_t m1;
  if (bBits < (uint32_t)64U * bLen)
  {
    KRML_CHECK_SIZE(sizeof (uint64_t), bLen);
    uint64_t *b2 = alloca(bLen * sizeof (uint64_t));
    memset(b2, 0U, bLen * sizeof (uint64_t));
    uint32_t i0 = bBits / (uint32_t)64U;
    uint32_t j = bBits % (uint32_t)64U;
    b2[i0] = b2[i0] | (uint64_t)1U << j;
    uint64_t acc = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < bLen; i++)
    {
      uint64_t beq = FStar_UInt64_eq_mask(b[i], b2[i]);
      uint64_t blt = ~FStar_UInt64_gte_mask(b[i], b2[i]);
      acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
    }
    uint64_t res = acc;
    m1 = res;
  }
  else
  {
    m1 = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  }
  uint64_t acc = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(a[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t m2 = acc;
  uint64_t m = m1 & m2;
  return m00 & m;
}

static inline void
exp_vartime_precomp(
  uint64_t *n,
  uint64_t mu,
  uint64_t *r2,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  if (bBits < (uint32_t)200U)
  {
    uint64_t aM[4U] = { 0U };
    uint64_t c[8U] = { 0U };
    Hacl_Bignum256_mul(a, r2, c);
    reduction(n, mu, c, aM);
    uint64_t resM[4U] = { 0U };
    uint64_t tmp0[8U] = { 0U };
    memcpy(tmp0, r2, (uint32_t)4U * sizeof (uint64_t));
    reduction(n, mu, tmp0, resM);
    for (uint32_t i = (uint32_t)0U; i < bBits; i++)
    {
      uint32_t i1 = i / (uint32_t)64U;
      uint32_t j = i % (uint32_t)64U;
      uint64_t tmp = b[i1];
      uint64_t bit = tmp >> j & (uint64_t)1U;
      if (!(bit == (uint64_t)0U))
      {
        amont_mul(n, mu, resM, aM, resM);
      }
      amont_sqr(n, mu, aM, aM);
    }
    uint64_t tmp[8U] = { 0U };
    memcpy(tmp, resM, (uint32_t)4U * sizeof (uint64_t));
    reduction(n, mu, tmp, res);
    return;
  }
  uint64_t aM[4U] = { 0U };
  uint64_t c[8U] = { 0U };
  Hacl_Bignum256_mul(a, r2, c);
  reduction(n, mu, c, aM);
  uint64_t resM[4U] = { 0U };
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  }
  uint64_t tmp[8U] = { 0U };
  memcpy(tmp, r2, (uint32_t)4U * sizeof (uint64_t));
  reduction(n, mu, tmp, resM);
  uint32_t table_len = (uint32_t)16U;
  KRML_CHECK_SIZE(sizeof (uint64_t), table_len * (uint32_t)4U);
  uint64_t *table = alloca(table_len * (uint32_t)4U * sizeof (uint64_t));
  memset(table, 0U, table_len * (uint32_t)4U * sizeof (uint64_t));
  memcpy(table, resM, (uint32_t)4U * sizeof (uint64_t));
  uint64_t *t1 = table + (uint32_t)4U;
  memcpy(t1, aM, (uint32_t)4U * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < table_len - (uint32_t)2U; i++)
  {
    uint64_t *t11 = table + (i + (uint32_t)1U) * (uint32_t)4U;
    uint64_t *t2 = table + (i + (uint32_t)2U) * (uint32_t)4U;
    amont_mul(n, mu, t11, aM, t2);
  }
  for (uint32_t i = (uint32_t)0U; i < bBits / (uint32_t)4U; i++)
  {
    for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
    {
      amont_sqr(n, mu, resM, resM);
    }
    uint64_t mask_l = (uint64_t)16U - (uint64_t)1U;
    uint32_t i1 = (bBits - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)64U;
    uint32_t j = (bBits - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)64U;
    uint64_t p1 = b[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l = ite & mask_l;
    uint32_t bits_l32 = (uint32_t)bits_l;
    uint64_t *a_bits_l = table + bits_l32 * (uint32_t)4U;
    amont_mul(n, mu, resM, a_bits_l, resM);
  }
  if (!(bBits % (uint32_t)4U == (uint32_t)0U))
  {
    uint32_t c0 = bBits % (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < c0; i++)
    {
      amont_sqr(n, mu, resM, resM);
    }
    uint32_t c1 = bBits % (uint32_t)4U;
    uint64_t mask_l = ((uint64_t)1U << c1) - (uint64_t)1U;
    uint32_t i = (uint32_t)0U;
    uint32_t j = (uint32_t)0U;
    uint64_t p1 = b[i] >> j;
    uint64_t ite;
    if (i + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_c = ite & mask_l;
    uint64_t bits_c0 = bits_c;
    uint32_t bits_c32 = (uint32_t)bits_c0;
    uint64_t *a_bits_c = table + bits_c32 * (uint32_t)4U;
    amont_mul(n, mu, resM, a_bits_c, resM);
  }
  uint64_t tmp0[8U] = { 0U };
  memcpy(tmp0, resM, (uint32_t)4U * sizeof (uint64_t));
  reduction(n, mu, tmp0, res);
}

static inline void
exp_consttime_precomp(
  uint64_t *n,
  uint64_t mu,
  uint64_t *r2,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  if (bBits < (uint32_t)200U)
  {
    uint64_t aM[4U] = { 0U };
    uint64_t c[8U] = { 0U };
    Hacl_Bignum256_mul(a, r2, c);
    reduction(n, mu, c, aM);
    uint64_t resM[4U] = { 0U };
    uint64_t tmp0[8U] = { 0U };
    memcpy(tmp0, r2, (uint32_t)4U * sizeof (uint64_t));
    reduction(n, mu, tmp0, resM);
    uint64_t sw = (uint64_t)0U;
    for (uint32_t i0 = (uint32_t)0U; i0 < bBits; i0++)
    {
      uint32_t i1 = (bBits - i0 - (uint32_t)1U) / (uint32_t)64U;
      uint32_t j = (bBits - i0 - (uint32_t)1U) % (uint32_t)64U;
      uint64_t tmp = b[i1];
      uint64_t bit = tmp >> j & (uint64_t)1U;
      uint64_t sw1 = bit ^ sw;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t dummy = ((uint64_t)0U - sw1) & (resM[i] ^ aM[i]);
        resM[i] = resM[i] ^ dummy;
        aM[i] = aM[i] ^ dummy;
      }
      amont_mul(n, mu, aM, resM, aM);
      amont_sqr(n, mu, resM, resM);
      sw = bit;
    }
    uint64_t sw0 = sw;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t dummy = ((uint64_t)0U - sw0) & (resM[i] ^ aM[i]);
      resM[i] = resM[i] ^ dummy;
      aM[i] = aM[i] ^ dummy;
    }
    uint64_t tmp[8U] = { 0U };
    memcpy(tmp, resM, (uint32_t)4U * sizeof (uint64_t));
    reduction(n, mu, tmp, res);
    return;
  }
  uint64_t aM[4U] = { 0U };
  uint64_t c0[8U] = { 0U };
  Hacl_Bignum256_mul(a, r2, c0);
  reduction(n, mu, c0, aM);
  uint64_t resM[4U] = { 0U };
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  }
  uint64_t tmp[8U] = { 0U };
  memcpy(tmp, r2, (uint32_t)4U * sizeof (uint64_t));
  reduction(n, mu, tmp, resM);
  uint32_t table_len = (uint32_t)16U;
  KRML_CHECK_SIZE(sizeof (uint64_t), table_len * (uint32_t)4U);
  uint64_t *table = alloca(table_len * (uint32_t)4U * sizeof (uint64_t));
  memset(table, 0U, table_len * (uint32_t)4U * sizeof (uint64_t));
  memcpy(table, resM, (uint32_t)4U * sizeof (uint64_t));
  uint64_t *t1 = table + (uint32_t)4U;
  memcpy(t1, aM, (uint32_t)4U * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < table_len - (uint32_t)2U; i++)
  {
    uint64_t *t11 = table + (i + (uint32_t)1U) * (uint32_t)4U;
    uint64_t *t2 = table + (i + (uint32_t)2U) * (uint32_t)4U;
    amont_mul(n, mu, t11, aM, t2);
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < bBits / (uint32_t)4U; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      amont_sqr(n, mu, resM, resM);
    }
    uint64_t mask_l = (uint64_t)16U - (uint64_t)1U;
    uint32_t i1 = (bBits - (uint32_t)4U * i0 - (uint32_t)4U) / (uint32_t)64U;
    uint32_t j = (bBits - (uint32_t)4U * i0 - (uint32_t)4U) % (uint32_t)64U;
    uint64_t p1 = b[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l = ite & mask_l;
    uint64_t a_bits_l[4U] = { 0U };
    memcpy(a_bits_l, table, (uint32_t)4U * sizeof (uint64_t));
    for (uint32_t i2 = (uint32_t)0U; i2 < table_len - (uint32_t)1U; i2++)
    {
      uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i2 + (uint32_t)1U));
      uint64_t *res_j = table + (i2 + (uint32_t)1U) * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = a_bits_l;
        uint64_t x = (c & res_j[i]) | (~c & a_bits_l[i]);
        os[i] = x;
      }
    }
    amont_mul(n, mu, resM, a_bits_l, resM);
  }
  if (!(bBits % (uint32_t)4U == (uint32_t)0U))
  {
    uint32_t c = bBits % (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < c; i++)
    {
      amont_sqr(n, mu, resM, resM);
    }
    uint32_t c10 = bBits % (uint32_t)4U;
    uint64_t mask_l = ((uint64_t)1U << c10) - (uint64_t)1U;
    uint32_t i0 = (uint32_t)0U;
    uint32_t j = (uint32_t)0U;
    uint64_t p1 = b[i0] >> j;
    uint64_t ite;
    if (i0 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i0 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_c = ite & mask_l;
    uint64_t bits_c0 = bits_c;
    uint64_t a_bits_c[4U] = { 0U };
    memcpy(a_bits_c, table, (uint32_t)4U * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < table_len - (uint32_t)1U; i1++)
    {
      uint64_t c1 = FStar_UInt64_eq_mask(bits_c0, (uint64_t)(i1 + (uint32_t)1U));
      uint64_t *res_j = table + (i1 + (uint32_t)1U) * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = a_bits_c;
        uint64_t x = (c1 & res_j[i]) | (~c1 & a_bits_c[i]);
        os[i] = x;
      }
    }
    amont_mul(n, mu, resM, a_bits_c, resM);
  }
  uint64_t tmp0[8U] = { 0U };
  memcpy(tmp0, resM, (uint32_t)4U * sizeof (uint64_t));
  reduction(n, mu, tmp0, res);
}

static inline void
exp_vartime(
  uint32_t nBits,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t r2[4U] = { 0U };
  precompr2(nBits, n, r2);
  uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  exp_vartime_precomp(n, mu, r2, a, bBits, b, res);
}

static inline void
exp_consttime(
  uint32_t nBits,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t r2[4U] = { 0U };
  precompr2(nBits, n, r2);
  uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  exp_consttime_precomp(n, mu, r2, a, bBits, b, res);
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • b < pow2 bBits
   • a < n 
*/
bool
Hacl_Bignum256_mod_exp_vartime(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t is_valid_m = exp_check(n, a, bBits, b);
  uint32_t
  nBits = (uint32_t)64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64((uint32_t)4U, n);
  if (is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU)
  {
    exp_vartime(nBits, n, a, bBits, b, res);
  }
  else
  {
    memset(res, 0U, (uint32_t)4U * sizeof (uint64_t));
  }
  return is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • b < pow2 bBits
   • a < n 
*/
bool
Hacl_Bignum256_mod_exp_consttime(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t is_valid_m = exp_check(n, a, bBits, b);
  uint32_t
  nBits = (uint32_t)64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64((uint32_t)4U, n);
  if (is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU)
  {
    exp_consttime(nBits, n, a, bBits, b, res);
  }
  else
  {
    memset(res, 0U, (uint32_t)4U * sizeof (uint64_t));
  }
  return is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}

/*
Write `a ^ (-1) mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime

  The function returns false if any of the following preconditions are violated, true otherwise.
  • n % 2 = 1
  • 1 < n
  • 0 < a
  • a < n 
*/
bool Hacl_Bignum256_mod_inv_prime_vartime(uint64_t *n, uint64_t *a, uint64_t *res)
{
  uint64_t one[4U] = { 0U };
  memset(one, 0U, (uint32_t)4U * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint64_t bit0 = n[0U] & (uint64_t)1U;
  uint64_t m0 = (uint64_t)0U - bit0;
  uint64_t acc0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(one[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(one[i], n[i]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t m1 = acc0;
  uint64_t m00 = m0 & m1;
  uint64_t bn_zero[4U] = { 0U };
  uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t uu____0 = FStar_UInt64_eq_mask(a[i], bn_zero[i]);
    mask = uu____0 & mask;
  }
  uint64_t mask1 = mask;
  uint64_t res10 = mask1;
  uint64_t m10 = res10;
  uint64_t acc = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(a[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t m2 = acc;
  uint64_t is_valid_m = (m00 & ~m10) & m2;
  uint32_t
  nBits = (uint32_t)64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64((uint32_t)4U, n);
  if (is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU)
  {
    uint64_t n2[4U] = { 0U };
    uint64_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64((uint64_t)0U, n[0U], (uint64_t)2U, n2);
    uint64_t c1;
    if ((uint32_t)1U < (uint32_t)4U)
    {
      uint32_t rLen = (uint32_t)3U;
      uint64_t *a1 = n + (uint32_t)1U;
      uint64_t *res1 = n2 + (uint32_t)1U;
      uint64_t c = c0;
      for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
      {
        uint64_t t1 = a1[(uint32_t)4U * i];
        uint64_t *res_i0 = res1 + (uint32_t)4U * i;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res_i0);
        uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, (uint64_t)0U, res_i1);
        uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, (uint64_t)0U, res_i2);
        uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, (uint64_t)0U, res_i);
      }
      for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
      {
        uint64_t t1 = a1[i];
        uint64_t *res_i = res1 + i;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res_i);
      }
      uint64_t c10 = c;
      c1 = c10;
    }
    else
    {
      c1 = c0;
    }
    exp_vartime(nBits, n, a, (uint32_t)256U, n2, res);
  }
  else
  {
    memset(res, 0U, (uint32_t)4U * sizeof (uint64_t));
  }
  return is_valid_m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}


/**********************************************/
/* Arithmetic functions with precomputations. */
/**********************************************/


/*
Heap-allocate and initialize a montgomery context.

  The argument n is meant to be a 256-bit bignum, i.e. uint64_t[4].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n % 2 = 1
  • 1 < n

  The caller will need to call Hacl_Bignum256_mont_ctx_free on the return value
  to avoid memory leaks.
*/
Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *Hacl_Bignum256_mont_ctx_init(uint64_t *n)
{
  uint64_t *r2 = KRML_HOST_CALLOC((uint32_t)4U, sizeof (uint64_t));
  uint64_t *n1 = KRML_HOST_CALLOC((uint32_t)4U, sizeof (uint64_t));
  uint64_t *r21 = r2;
  uint64_t *n11 = n1;
  memcpy(n11, n, (uint32_t)4U * sizeof (uint64_t));
  uint32_t
  nBits = (uint32_t)64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64((uint32_t)4U, n);
  precompr2(nBits, n, r21);
  uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64
  res = { .len = (uint32_t)4U, .n = n11, .mu = mu, .r2 = r21 };
  KRML_CHECK_SIZE(sizeof (Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64), (uint32_t)1U);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64
  *buf = KRML_HOST_MALLOC(sizeof (Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64));
  buf[0U] = res;
  return buf;
}

/*
Deallocate the memory previously allocated by Hacl_Bignum256_mont_ctx_init.

  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.
*/
void Hacl_Bignum256_mont_ctx_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  uint64_t *n = k1.n;
  uint64_t *r2 = k1.r2;
  KRML_HOST_FREE(n);
  KRML_HOST_FREE(r2);
  KRML_HOST_FREE(k);
}

/*
Write `a mod n` in `res`.

  The argument a is meant to be a 512-bit bignum, i.e. uint64_t[8].
  The outparam res is meant to be a 256-bit bignum, i.e. uint64_t[4].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.
*/
void
Hacl_Bignum256_mod_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  bn_slow_precomp(k1.n, k1.mu, k1.r2, a, res);
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n 
*/
void
Hacl_Bignum256_mod_exp_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  exp_vartime_precomp(k1.n, k1.mu, k1.r2, a, bBits, b, res);
}

/*
Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime_*.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n 
*/
void
Hacl_Bignum256_mod_exp_consttime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  exp_consttime_precomp(k1.n, k1.mu, k1.r2, a, bBits, b, res);
}

/*
Write `a ^ (-1) mod n` in `res`.

  The argument a and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime
  • 0 < a
  • a < n 
*/
void
Hacl_Bignum256_mod_inv_prime_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  uint64_t n2[4U] = { 0U };
  uint64_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64((uint64_t)0U, k1.n[0U], (uint64_t)2U, n2);
  uint64_t c1;
  if ((uint32_t)1U < (uint32_t)4U)
  {
    uint32_t rLen = (uint32_t)3U;
    uint64_t *a1 = k1.n + (uint32_t)1U;
    uint64_t *res1 = n2 + (uint32_t)1U;
    uint64_t c = c0;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t t1 = a1[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res_i0);
      uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, (uint64_t)0U, res_i1);
      uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, (uint64_t)0U, res_i2);
      uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t1 = a1[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res_i);
    }
    uint64_t c10 = c;
    c1 = c10;
  }
  else
  {
    c1 = c0;
  }
  exp_vartime_precomp(k1.n, k1.mu, k1.r2, a, (uint32_t)256U, n2, res);
}


/********************/
/* Loads and stores */
/********************/


/*
Load a bid-endian bignum from memory.

  The argument b points to len bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint64_t *Hacl_Bignum256_new_bn_from_bytes_be(uint32_t len, uint8_t *b)
{
  if
  (
    len
    == (uint32_t)0U
    || !((len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U <= (uint32_t)536870911U)
  )
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U);
  uint64_t
  *res = KRML_HOST_CALLOC((len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, sizeof (uint64_t));
  if (res == NULL)
  {
    return res;
  }
  uint64_t *res1 = res;
  uint64_t *res2 = res1;
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp + tmpLen - len, b, len * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    uint64_t *os = res2;
    uint64_t u = load64_be(tmp + (bnLen - i - (uint32_t)1U) * (uint32_t)8U);
    uint64_t x = u;
    os[i] = x;
  }
  return res2;
}

/*
Load a little-endian bignum from memory.

  The argument b points to len bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint64_t *Hacl_Bignum256_new_bn_from_bytes_le(uint32_t len, uint8_t *b)
{
  if
  (
    len
    == (uint32_t)0U
    || !((len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U <= (uint32_t)536870911U)
  )
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U);
  uint64_t
  *res = KRML_HOST_CALLOC((len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, sizeof (uint64_t));
  if (res == NULL)
  {
    return res;
  }
  uint64_t *res1 = res;
  uint64_t *res2 = res1;
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp, b, len * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U; i++)
  {
    uint64_t *os = res2;
    uint8_t *bj = tmp + i * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r1 = u;
    uint64_t x = r1;
    os[i] = x;
  }
  return res2;
}

/*
Serialize a bignum into big-endian memory.

  The argument b points to a 256-bit bignum.
  The outparam res points to 32 bytes of valid memory.
*/
void Hacl_Bignum256_bn_to_bytes_be(uint64_t *b, uint8_t *res)
{
  uint32_t bnLen = ((uint32_t)32U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  uint32_t numb = (uint32_t)8U;
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    store64_be(tmp + i * numb, b[bnLen - i - (uint32_t)1U]);
  }
  memcpy(res, tmp + tmpLen - (uint32_t)32U, (uint32_t)32U * sizeof (uint8_t));
}

/*
Serialize a bignum into little-endian memory.

  The argument b points to a 256-bit bignum.
  The outparam res points to 32 bytes of valid memory.
*/
void Hacl_Bignum256_bn_to_bytes_le(uint64_t *b, uint8_t *res)
{
  uint32_t bnLen = ((uint32_t)32U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    store64_le(tmp + i * (uint32_t)8U, b[i]);
  }
  memcpy(res, tmp, (uint32_t)32U * sizeof (uint8_t));
}


/***************/
/* Comparisons */
/***************/


/*
Returns 2 ^ 64 - 1 if and only if the argument a is strictly less than the argument b,
 otherwise returns 0.
*/
uint64_t Hacl_Bignum256_lt_mask(uint64_t *a, uint64_t *b)
{
  uint64_t acc = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(a[i], b[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(a[i], b[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  return acc;
}

