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


#include "math/bigfix/Hacl_Bignum.h"

void Hacl_Bignum_Convert_bn_from_bytes_be_uint64(uint32_t len, uint8_t *b, uint64_t *res)
{
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp + tmpLen - len, b, len * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    uint64_t *os = res;
    uint64_t u = load64_be(tmp + (bnLen - i - (uint32_t)1U) * (uint32_t)8U);
    uint64_t x = u;
    os[i] = x;
  }
}

void Hacl_Bignum_Convert_bn_to_bytes_be_uint64(uint32_t len, uint64_t *b, uint8_t *res)
{
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  uint32_t numb = (uint32_t)8U;
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    store64_be(tmp + i * numb, b[bnLen - i - (uint32_t)1U]);
  }
  memcpy(res, tmp + tmpLen - len, len * sizeof (uint8_t));
}

uint32_t Hacl_Bignum_Lib_bn_get_top_index_u32(uint32_t len, uint32_t *b)
{
  uint32_t priv = (uint32_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint32_t mask = FStar_UInt32_eq_mask(b[i], (uint32_t)0U);
    priv = (mask & priv) | (~mask & i);
  }
  return priv;
}

uint64_t Hacl_Bignum_Lib_bn_get_top_index_u64(uint32_t len, uint64_t *b)
{
  uint64_t priv = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t mask = FStar_UInt64_eq_mask(b[i], (uint64_t)0U);
    priv = (mask & priv) | (~mask & (uint64_t)i);
  }
  return priv;
}

inline uint32_t
Hacl_Bignum_Addition_bn_sub_eq_len_u32(uint32_t aLen, uint32_t *a, uint32_t *b, uint32_t *res)
{
  uint32_t c = (uint32_t)0U;
  for (uint32_t i = (uint32_t)0U; i < aLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint32_t t1 = a[(uint32_t)4U * i];
    uint32_t t20 = b[(uint32_t)4U * i];
    uint32_t *res_i0 = res + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t20, res_i0);
    uint32_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, t21, res_i1);
    uint32_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, t22, res_i2);
    uint32_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, t2, res_i);
  }
  for (uint32_t i = aLen / (uint32_t)4U * (uint32_t)4U; i < aLen; i++)
  {
    uint32_t t1 = a[i];
    uint32_t t2 = b[i];
    uint32_t *res_i = res + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t2, res_i);
  }
  return c;
}

inline uint64_t
Hacl_Bignum_Addition_bn_sub_eq_len_u64(uint32_t aLen, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < aLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
  for (uint32_t i = aLen / (uint32_t)4U * (uint32_t)4U; i < aLen; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  return c;
}

inline uint32_t
Hacl_Bignum_Addition_bn_add_eq_len_u32(uint32_t aLen, uint32_t *a, uint32_t *b, uint32_t *res)
{
  uint32_t c = (uint32_t)0U;
  for (uint32_t i = (uint32_t)0U; i < aLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint32_t t1 = a[(uint32_t)4U * i];
    uint32_t t20 = b[(uint32_t)4U * i];
    uint32_t *res_i0 = res + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, t20, res_i0);
    uint32_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t10, t21, res_i1);
    uint32_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, t22, res_i2);
    uint32_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t12, t2, res_i);
  }
  for (uint32_t i = aLen / (uint32_t)4U * (uint32_t)4U; i < aLen; i++)
  {
    uint32_t t1 = a[i];
    uint32_t t2 = b[i];
    uint32_t *res_i = res + i;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, t2, res_i);
  }
  return c;
}

inline uint64_t
Hacl_Bignum_Addition_bn_add_eq_len_u64(uint32_t aLen, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < aLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
  for (uint32_t i = aLen / (uint32_t)4U * (uint32_t)4U; i < aLen; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, res_i);
  }
  return c;
}

static inline void
bn_mul_u32(uint32_t aLen, uint32_t *a, uint32_t bLen, uint32_t *b, uint32_t *res)
{
  uint32_t resLen = aLen + bLen;
  memset(res, 0U, resLen * sizeof (uint32_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < bLen; i0++)
  {
    uint32_t bj = b[i0];
    uint32_t *res_j = res + i0;
    uint32_t c = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < aLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint32_t a_i = a[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    }
    for (uint32_t i = aLen / (uint32_t)4U * (uint32_t)4U; i < aLen; i++)
    {
      uint32_t a_i = a[i];
      uint32_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i);
    }
    uint32_t r = c;
    res[aLen + i0] = r;
  }
}

static inline void
bn_mul_u64(uint32_t aLen, uint64_t *a, uint32_t bLen, uint64_t *b, uint64_t *res)
{
  uint32_t resLen = aLen + bLen;
  memset(res, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < bLen; i0++)
  {
    uint64_t bj = b[i0];
    uint64_t *res_j = res + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < aLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
    for (uint32_t i = aLen / (uint32_t)4U * (uint32_t)4U; i < aLen; i++)
    {
      uint64_t a_i = a[i];
      uint64_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i);
    }
    uint64_t r = c;
    res[aLen + i0] = r;
  }
}

static inline void bn_sqr_u32(uint32_t aLen, uint32_t *a, uint32_t *res)
{
  uint32_t resLen = aLen + aLen;
  memset(res, 0U, resLen * sizeof (uint32_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < aLen; i0++)
  {
    uint32_t *ab = a;
    uint32_t a_j = a[i0];
    uint32_t *res_j = res + i0;
    uint32_t c = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < i0 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = i0 / (uint32_t)4U * (uint32_t)4U; i < i0; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i);
    }
    uint32_t r = c;
    res[i0 + i0] = r;
  }
  uint32_t c0 = Hacl_Bignum_Addition_bn_add_eq_len_u32(resLen, res, res, res);
  (void)c0;
  KRML_CHECK_SIZE(sizeof (uint32_t), resLen);
  uint32_t *tmp = alloca(resLen * sizeof (uint32_t));
  memset(tmp, 0U, resLen * sizeof (uint32_t));
  for (uint32_t i = (uint32_t)0U; i < aLen; i++)
  {
    uint64_t res1 = (uint64_t)a[i] * (uint64_t)a[i];
    uint32_t hi = (uint32_t)(res1 >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res1;
    tmp[(uint32_t)2U * i] = lo;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;
  }
  uint32_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u32(resLen, res, tmp, res);
  (void)c1;
}

static inline void bn_sqr_u64(uint32_t aLen, uint64_t *a, uint64_t *res)
{
  uint32_t resLen = aLen + aLen;
  memset(res, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < aLen; i0++)
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
  (void)c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), resLen);
  uint64_t *tmp = alloca(resLen * sizeof (uint64_t));
  memset(tmp, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < aLen; i++)
  {
    FStar_UInt128_uint128 res1 = FStar_UInt128_mul_wide(a[i], a[i]);
    uint64_t hi = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
    uint64_t lo = FStar_UInt128_uint128_to_uint64(res1);
    tmp[(uint32_t)2U * i] = lo;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;
  }
  uint64_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u64(resLen, res, tmp, res);
  (void)c1;
}

void
Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(
  uint32_t aLen,
  uint32_t *a,
  uint32_t *b,
  uint32_t *tmp,
  uint32_t *res
)
{
  if (aLen < (uint32_t)32U || aLen % (uint32_t)2U == (uint32_t)1U)
  {
    bn_mul_u32(aLen, a, aLen, b, res);
    return;
  }
  uint32_t len2 = aLen / (uint32_t)2U;
  uint32_t *a0 = a;
  uint32_t *a1 = a + len2;
  uint32_t *b0 = b;
  uint32_t *b1 = b + len2;
  uint32_t *t0 = tmp;
  uint32_t *t1 = tmp + len2;
  uint32_t *tmp_ = tmp + aLen;
  uint32_t c0 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a0, a1, tmp_);
  uint32_t c10 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a1, a0, t0);
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint32_t *os = t0;
    uint32_t x = (((uint32_t)0U - c0) & t0[i]) | (~((uint32_t)0U - c0) & tmp_[i]);
    os[i] = x;
  }
  uint32_t c00 = c0;
  uint32_t c010 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, b0, b1, tmp_);
  uint32_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, b1, b0, t1);
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint32_t *os = t1;
    uint32_t x = (((uint32_t)0U - c010) & t1[i]) | (~((uint32_t)0U - c010) & tmp_[i]);
    os[i] = x;
  }
  uint32_t c11 = c010;
  uint32_t *t23 = tmp + aLen;
  uint32_t *tmp1 = tmp + aLen + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len2, t0, t1, tmp1, t23);
  uint32_t *r01 = res;
  uint32_t *r23 = res + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len2, a0, b0, tmp1, r01);
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len2, a1, b1, tmp1, r23);
  uint32_t *r011 = res;
  uint32_t *r231 = res + aLen;
  uint32_t *t01 = tmp;
  uint32_t *t231 = tmp + aLen;
  uint32_t *t45 = tmp + (uint32_t)2U * aLen;
  uint32_t *t67 = tmp + (uint32_t)3U * aLen;
  uint32_t c2 = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, r011, r231, t01);
  uint32_t c_sign = c00 ^ c11;
  uint32_t c3 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(aLen, t01, t231, t67);
  uint32_t c31 = c2 - c3;
  uint32_t c4 = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, t01, t231, t45);
  uint32_t c41 = c2 + c4;
  uint32_t mask = (uint32_t)0U - c_sign;
  for (uint32_t i = (uint32_t)0U; i < aLen; i++)
  {
    uint32_t *os = t45;
    uint32_t x = (mask & t45[i]) | (~mask & t67[i]);
    os[i] = x;
  }
  uint32_t c5 = (mask & c41) | (~mask & c31);
  uint32_t aLen2 = aLen / (uint32_t)2U;
  uint32_t *r0 = res + aLen2;
  uint32_t r10 = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, r0, t45, r0);
  uint32_t c6 = r10;
  uint32_t c60 = c6;
  uint32_t c7 = c5 + c60;
  uint32_t *r = res + aLen + aLen2;
  uint32_t c01 = Lib_IntTypes_Intrinsics_add_carry_u32((uint32_t)0U, r[0U], c7, r);
  uint32_t r1;
  if ((uint32_t)1U < aLen + aLen - (aLen + aLen2))
  {
    uint32_t rLen = aLen + aLen - (aLen + aLen2) - (uint32_t)1U;
    uint32_t *a11 = r + (uint32_t)1U;
    uint32_t *res1 = r + (uint32_t)1U;
    uint32_t c = c01;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint32_t t11 = a11[(uint32_t)4U * i];
      uint32_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, (uint32_t)0U, res_i0);
      uint32_t t110 = a11[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t110, (uint32_t)0U, res_i1);
      uint32_t t111 = a11[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t111, (uint32_t)0U, res_i2);
      uint32_t t112 = a11[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t112, (uint32_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint32_t t11 = a11[i];
      uint32_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, (uint32_t)0U, res_i);
    }
    uint32_t c110 = c;
    r1 = c110;
  }
  else
  {
    r1 = c01;
  }
  uint32_t c8 = r1;
  uint32_t c = c8;
  uint32_t c9 = c;
}

void
Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(
  uint32_t aLen,
  uint64_t *a,
  uint64_t *b,
  uint64_t *tmp,
  uint64_t *res
)
{
  if (aLen < (uint32_t)32U || aLen % (uint32_t)2U == (uint32_t)1U)
  {
    bn_mul_u64(aLen, a, aLen, b, res);
    return;
  }
  uint32_t len2 = aLen / (uint32_t)2U;
  uint64_t *a0 = a;
  uint64_t *a1 = a + len2;
  uint64_t *b0 = b;
  uint64_t *b1 = b + len2;
  uint64_t *t0 = tmp;
  uint64_t *t1 = tmp + len2;
  uint64_t *tmp_ = tmp + aLen;
  uint64_t c0 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a0, a1, tmp_);
  uint64_t c10 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a1, a0, t0);
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t *os = t0;
    uint64_t x = (((uint64_t)0U - c0) & t0[i]) | (~((uint64_t)0U - c0) & tmp_[i]);
    os[i] = x;
  }
  uint64_t c00 = c0;
  uint64_t c010 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, b0, b1, tmp_);
  uint64_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, b1, b0, t1);
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t *os = t1;
    uint64_t x = (((uint64_t)0U - c010) & t1[i]) | (~((uint64_t)0U - c010) & tmp_[i]);
    os[i] = x;
  }
  uint64_t c11 = c010;
  uint64_t *t23 = tmp + aLen;
  uint64_t *tmp1 = tmp + aLen + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len2, t0, t1, tmp1, t23);
  uint64_t *r01 = res;
  uint64_t *r23 = res + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len2, a0, b0, tmp1, r01);
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len2, a1, b1, tmp1, r23);
  uint64_t *r011 = res;
  uint64_t *r231 = res + aLen;
  uint64_t *t01 = tmp;
  uint64_t *t231 = tmp + aLen;
  uint64_t *t45 = tmp + (uint32_t)2U * aLen;
  uint64_t *t67 = tmp + (uint32_t)3U * aLen;
  uint64_t c2 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r011, r231, t01);
  uint64_t c_sign = c00 ^ c11;
  uint64_t c3 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(aLen, t01, t231, t67);
  uint64_t c31 = c2 - c3;
  uint64_t c4 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, t01, t231, t45);
  uint64_t c41 = c2 + c4;
  uint64_t mask = (uint64_t)0U - c_sign;
  for (uint32_t i = (uint32_t)0U; i < aLen; i++)
  {
    uint64_t *os = t45;
    uint64_t x = (mask & t45[i]) | (~mask & t67[i]);
    os[i] = x;
  }
  uint64_t c5 = (mask & c41) | (~mask & c31);
  uint32_t aLen2 = aLen / (uint32_t)2U;
  uint64_t *r0 = res + aLen2;
  uint64_t r10 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r0, t45, r0);
  uint64_t c6 = r10;
  uint64_t c60 = c6;
  uint64_t c7 = c5 + c60;
  uint64_t *r = res + aLen + aLen2;
  uint64_t c01 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, r[0U], c7, r);
  uint64_t r1;
  if ((uint32_t)1U < aLen + aLen - (aLen + aLen2))
  {
    uint32_t rLen = aLen + aLen - (aLen + aLen2) - (uint32_t)1U;
    uint64_t *a11 = r + (uint32_t)1U;
    uint64_t *res1 = r + (uint32_t)1U;
    uint64_t c = c01;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t t11 = a11[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i0);
      uint64_t t110 = a11[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t110, (uint64_t)0U, res_i1);
      uint64_t t111 = a11[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t111, (uint64_t)0U, res_i2);
      uint64_t t112 = a11[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t112, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t11 = a11[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i);
    }
    uint64_t c110 = c;
    r1 = c110;
  }
  else
  {
    r1 = c01;
  }
  uint64_t c8 = r1;
  uint64_t c = c8;
  uint64_t c9 = c;
}

void
Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(
  uint32_t aLen,
  uint32_t *a,
  uint32_t *tmp,
  uint32_t *res
)
{
  if (aLen < (uint32_t)32U || aLen % (uint32_t)2U == (uint32_t)1U)
  {
    bn_sqr_u32(aLen, a, res);
    return;
  }
  uint32_t len2 = aLen / (uint32_t)2U;
  uint32_t *a0 = a;
  uint32_t *a1 = a + len2;
  uint32_t *t0 = tmp;
  uint32_t *tmp_ = tmp + aLen;
  uint32_t c0 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a0, a1, tmp_);
  uint32_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a1, a0, t0);
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint32_t *os = t0;
    uint32_t x = (((uint32_t)0U - c0) & t0[i]) | (~((uint32_t)0U - c0) & tmp_[i]);
    os[i] = x;
  }
  uint32_t c00 = c0;
  uint32_t *t23 = tmp + aLen;
  uint32_t *tmp1 = tmp + aLen + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(len2, t0, tmp1, t23);
  uint32_t *r01 = res;
  uint32_t *r23 = res + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(len2, a0, tmp1, r01);
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(len2, a1, tmp1, r23);
  uint32_t *r011 = res;
  uint32_t *r231 = res + aLen;
  uint32_t *t01 = tmp;
  uint32_t *t231 = tmp + aLen;
  uint32_t *t45 = tmp + (uint32_t)2U * aLen;
  uint32_t c2 = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, r011, r231, t01);
  uint32_t c3 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(aLen, t01, t231, t45);
  uint32_t c5 = c2 - c3;
  uint32_t aLen2 = aLen / (uint32_t)2U;
  uint32_t *r0 = res + aLen2;
  uint32_t r10 = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, r0, t45, r0);
  uint32_t c4 = r10;
  uint32_t c6 = c4;
  uint32_t c7 = c5 + c6;
  uint32_t *r = res + aLen + aLen2;
  uint32_t c01 = Lib_IntTypes_Intrinsics_add_carry_u32((uint32_t)0U, r[0U], c7, r);
  uint32_t r1;
  if ((uint32_t)1U < aLen + aLen - (aLen + aLen2))
  {
    uint32_t rLen = aLen + aLen - (aLen + aLen2) - (uint32_t)1U;
    uint32_t *a11 = r + (uint32_t)1U;
    uint32_t *res1 = r + (uint32_t)1U;
    uint32_t c = c01;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint32_t t1 = a11[(uint32_t)4U * i];
      uint32_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, (uint32_t)0U, res_i0);
      uint32_t t10 = a11[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t10, (uint32_t)0U, res_i1);
      uint32_t t11 = a11[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, (uint32_t)0U, res_i2);
      uint32_t t12 = a11[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t12, (uint32_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint32_t t1 = a11[i];
      uint32_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, (uint32_t)0U, res_i);
    }
    uint32_t c10 = c;
    r1 = c10;
  }
  else
  {
    r1 = c01;
  }
  uint32_t c8 = r1;
  uint32_t c = c8;
  uint32_t c9 = c;
}

void
Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(
  uint32_t aLen,
  uint64_t *a,
  uint64_t *tmp,
  uint64_t *res
)
{
  if (aLen < (uint32_t)32U || aLen % (uint32_t)2U == (uint32_t)1U)
  {
    bn_sqr_u64(aLen, a, res);
    return;
  }
  uint32_t len2 = aLen / (uint32_t)2U;
  uint64_t *a0 = a;
  uint64_t *a1 = a + len2;
  uint64_t *t0 = tmp;
  uint64_t *tmp_ = tmp + aLen;
  uint64_t c0 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a0, a1, tmp_);
  uint64_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a1, a0, t0);
  (void)c1;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t *os = t0;
    uint64_t x = (((uint64_t)0U - c0) & t0[i]) | (~((uint64_t)0U - c0) & tmp_[i]);
    os[i] = x;
  }
  uint64_t c00 = c0;
  (void)c00;
  uint64_t *t23 = tmp + aLen;
  uint64_t *tmp1 = tmp + aLen + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len2, t0, tmp1, t23);
  uint64_t *r01 = res;
  uint64_t *r23 = res + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len2, a0, tmp1, r01);
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len2, a1, tmp1, r23);
  uint64_t *r011 = res;
  uint64_t *r231 = res + aLen;
  uint64_t *t01 = tmp;
  uint64_t *t231 = tmp + aLen;
  uint64_t *t45 = tmp + (uint32_t)2U * aLen;
  uint64_t c2 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r011, r231, t01);
  uint64_t c3 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(aLen, t01, t231, t45);
  uint64_t c5 = c2 - c3;
  uint32_t aLen2 = aLen / (uint32_t)2U;
  uint64_t *r0 = res + aLen2;
  uint64_t r10 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r0, t45, r0);
  uint64_t c4 = r10;
  uint64_t c6 = c4;
  uint64_t c7 = c5 + c6;
  uint64_t *r = res + aLen + aLen2;
  uint64_t c01 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, r[0U], c7, r);
  uint64_t r1;
  if ((uint32_t)1U < aLen + aLen - (aLen + aLen2))
  {
    uint32_t rLen = aLen + aLen - (aLen + aLen2) - (uint32_t)1U;
    uint64_t *a11 = r + (uint32_t)1U;
    uint64_t *res1 = r + (uint32_t)1U;
    uint64_t c = c01;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t t1 = a11[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i0);
      uint64_t t10 = a11[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (uint64_t)0U, res_i1);
      uint64_t t11 = a11[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i2);
      uint64_t t12 = a11[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t1 = a11[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i);
    }
    uint64_t c10 = c;
    r1 = c10;
  }
  else
  {
    r1 = c01;
  }
  uint64_t c8 = r1;
  uint64_t c = c8;
  uint64_t c9 = c;
}

inline void
Hacl_Bignum_bn_add_mod_n_u32(
  uint32_t len1,
  uint32_t *n,
  uint32_t *a,
  uint32_t *b,
  uint32_t *res
)
{
  uint32_t c0 = (uint32_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint32_t t1 = a[(uint32_t)4U * i];
    uint32_t t20 = b[(uint32_t)4U * i];
    uint32_t *res_i0 = res + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t1, t20, res_i0);
    uint32_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t10, t21, res_i1);
    uint32_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t11, t22, res_i2);
    uint32_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t12, t2, res_i);
  }
  for (uint32_t i = len1 / (uint32_t)4U * (uint32_t)4U; i < len1; i++)
  {
    uint32_t t1 = a[i];
    uint32_t t2 = b[i];
    uint32_t *res_i = res + i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t1, t2, res_i);
  }
  uint32_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint32_t), len1);
  uint32_t *tmp = alloca(len1 * sizeof (uint32_t));
  memset(tmp, 0U, len1 * sizeof (uint32_t));
  uint32_t c = (uint32_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint32_t t1 = res[(uint32_t)4U * i];
    uint32_t t20 = n[(uint32_t)4U * i];
    uint32_t *res_i0 = tmp + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t20, res_i0);
    uint32_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t *res_i1 = tmp + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, t21, res_i1);
    uint32_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t *res_i2 = tmp + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, t22, res_i2);
    uint32_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t *res_i = tmp + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, t2, res_i);
  }
  for (uint32_t i = len1 / (uint32_t)4U * (uint32_t)4U; i < len1; i++)
  {
    uint32_t t1 = res[i];
    uint32_t t2 = n[i];
    uint32_t *res_i = tmp + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t2, res_i);
  }
  uint32_t c1 = c;
  uint32_t c2 = c00 - c1;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

inline void
Hacl_Bignum_bn_add_mod_n_u64(
  uint32_t len1,
  uint64_t *n,
  uint64_t *a,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
  for (uint32_t i = len1 / (uint32_t)4U * (uint32_t)4U; i < len1; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res_i);
  }
  uint64_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t *tmp = alloca(len1 * sizeof (uint64_t));
  memset(tmp, 0U, len1 * sizeof (uint64_t));
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
  for (uint32_t i = len1 / (uint32_t)4U * (uint32_t)4U; i < len1; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    uint64_t *res_i = tmp + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t c1 = c;
  uint64_t c2 = c00 - c1;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

inline uint32_t Hacl_Bignum_ModInvLimb_mod_inv_uint32(uint32_t n0)
{
  uint32_t alpha = (uint32_t)2147483648U;
  uint32_t beta = n0;
  uint32_t ub = (uint32_t)0U;
  uint32_t vb = (uint32_t)0U;
  ub = (uint32_t)1U;
  vb = (uint32_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
  {
    uint32_t us = ub;
    uint32_t vs = vb;
    uint32_t u_is_odd = (uint32_t)0U - (us & (uint32_t)1U);
    uint32_t beta_if_u_is_odd = beta & u_is_odd;
    ub = ((us ^ beta_if_u_is_odd) >> (uint32_t)1U) + (us & beta_if_u_is_odd);
    uint32_t alpha_if_u_is_odd = alpha & u_is_odd;
    vb = (vs >> (uint32_t)1U) + alpha_if_u_is_odd;
  }
  return vb;
}

inline uint64_t Hacl_Bignum_ModInvLimb_mod_inv_uint64(uint64_t n0)
{
  uint64_t alpha = (uint64_t)9223372036854775808U;
  uint64_t beta = n0;
  uint64_t ub = (uint64_t)0U;
  uint64_t vb = (uint64_t)0U;
  ub = (uint64_t)1U;
  vb = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t us = ub;
    uint64_t vs = vb;
    uint64_t u_is_odd = (uint64_t)0U - (us & (uint64_t)1U);
    uint64_t beta_if_u_is_odd = beta & u_is_odd;
    ub = ((us ^ beta_if_u_is_odd) >> (uint32_t)1U) + (us & beta_if_u_is_odd);
    uint64_t alpha_if_u_is_odd = alpha & u_is_odd;
    vb = (vs >> (uint32_t)1U) + alpha_if_u_is_odd;
  }
  return vb;
}

uint32_t Hacl_Bignum_Montgomery_bn_check_modulus_u32(uint32_t len, uint32_t *n)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *one = alloca(len * sizeof (uint32_t));
  memset(one, 0U, len * sizeof (uint32_t));
  memset(one, 0U, len * sizeof (uint32_t));
  one[0U] = (uint32_t)1U;
  uint32_t bit0 = n[0U] & (uint32_t)1U;
  uint32_t m0 = (uint32_t)0U - bit0;
  uint32_t acc = (uint32_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  uint32_t m1 = acc;
  return m0 & m1;
}

void
Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32(
  uint32_t len,
  uint32_t nBits,
  uint32_t *n,
  uint32_t *res
)
{
  memset(res, 0U, len * sizeof (uint32_t));
  uint32_t i = nBits / (uint32_t)32U;
  uint32_t j = nBits % (uint32_t)32U;
  res[i] = res[i] | (uint32_t)1U << j;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)64U * len - nBits; i0++)
  {
    Hacl_Bignum_bn_add_mod_n_u32(len, n, res, res, res);
  }
}

void
Hacl_Bignum_Montgomery_bn_mont_reduction_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv,
  uint32_t *c,
  uint32_t *res
)
{
  uint32_t c0 = (uint32_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
  {
    uint32_t qj = nInv * c[i0];
    uint32_t *res_j0 = c + i0;
    uint32_t c1 = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint32_t a_i = n[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    for (uint32_t i = len / (uint32_t)4U * (uint32_t)4U; i < len; i++)
    {
      uint32_t a_i = n[i];
      uint32_t *res_i = res_j0 + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + len + i0;
    uint32_t res_j = c[len + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  memcpy(res, c + len, (len + len - len) * sizeof (uint32_t));
  uint32_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *tmp = alloca(len * sizeof (uint32_t));
  memset(tmp, 0U, len * sizeof (uint32_t));
  uint32_t c1 = (uint32_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint32_t t1 = res[(uint32_t)4U * i];
    uint32_t t20 = n[(uint32_t)4U * i];
    uint32_t *res_i0 = tmp + (uint32_t)4U * i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t1, t20, res_i0);
    uint32_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t *res_i1 = tmp + (uint32_t)4U * i + (uint32_t)1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t10, t21, res_i1);
    uint32_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t *res_i2 = tmp + (uint32_t)4U * i + (uint32_t)2U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t11, t22, res_i2);
    uint32_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t *res_i = tmp + (uint32_t)4U * i + (uint32_t)3U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t12, t2, res_i);
  }
  for (uint32_t i = len / (uint32_t)4U * (uint32_t)4U; i < len; i++)
  {
    uint32_t t1 = res[i];
    uint32_t t2 = n[i];
    uint32_t *res_i = tmp + i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t1, t2, res_i);
  }
  uint32_t c10 = c1;
  uint32_t c2 = c00 - c10;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

void
Hacl_Bignum_Montgomery_bn_to_mont_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv,
  uint32_t *r2,
  uint32_t *a,
  uint32_t *aM
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t *c = alloca((len + len) * sizeof (uint32_t));
  memset(c, 0U, (len + len) * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * len);
  uint32_t *tmp = alloca((uint32_t)4U * len * sizeof (uint32_t));
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint32_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len, a, r2, tmp, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, nInv, c, aM);
}

void
Hacl_Bignum_Montgomery_bn_from_mont_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv_u64,
  uint32_t *aM,
  uint32_t *a
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t *tmp = alloca((len + len) * sizeof (uint32_t));
  memset(tmp, 0U, (len + len) * sizeof (uint32_t));
  memcpy(tmp, aM, len * sizeof (uint32_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, nInv_u64, tmp, a);
}

void
Hacl_Bignum_Montgomery_bn_mont_mul_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv_u64,
  uint32_t *aM,
  uint32_t *bM,
  uint32_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t *c = alloca((len + len) * sizeof (uint32_t));
  memset(c, 0U, (len + len) * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * len);
  uint32_t *tmp = alloca((uint32_t)4U * len * sizeof (uint32_t));
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint32_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len, aM, bM, tmp, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, nInv_u64, c, resM);
}

void
Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv_u64,
  uint32_t *aM,
  uint32_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t *c = alloca((len + len) * sizeof (uint32_t));
  memset(c, 0U, (len + len) * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * len);
  uint32_t *tmp = alloca((uint32_t)4U * len * sizeof (uint32_t));
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint32_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(len, aM, tmp, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, nInv_u64, c, resM);
}

uint64_t Hacl_Bignum_Montgomery_bn_check_modulus_u64(uint32_t len, uint64_t *n)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t *one = alloca(len * sizeof (uint64_t));
  memset(one, 0U, len * sizeof (uint64_t));
  memset(one, 0U, len * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint64_t bit0 = n[0U] & (uint64_t)1U;
  uint64_t m0 = (uint64_t)0U - bit0;
  uint64_t acc = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(one[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(one[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t m1 = acc;
  return m0 & m1;
}

void
Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(
  uint32_t len,
  uint32_t nBits,
  uint64_t *n,
  uint64_t *res
)
{
  memset(res, 0U, len * sizeof (uint64_t));
  uint32_t i = nBits / (uint32_t)64U;
  uint32_t j = nBits % (uint32_t)64U;
  res[i] = res[i] | (uint64_t)1U << j;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)128U * len - nBits; i0++)
  {
    Hacl_Bignum_bn_add_mod_n_u64(len, n, res, res, res);
  }
}

void
Hacl_Bignum_Montgomery_bn_mont_reduction_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv,
  uint64_t *c,
  uint64_t *res
)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
  {
    uint64_t qj = nInv * c[i0];
    uint64_t *res_j0 = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
    for (uint32_t i = len / (uint32_t)4U * (uint32_t)4U; i < len; i++)
    {
      uint64_t a_i = n[i];
      uint64_t *res_i = res_j0 + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i);
    }
    uint64_t r = c1;
    uint64_t c10 = r;
    uint64_t *resb = c + len + i0;
    uint64_t res_j = c[len + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c10, res_j, resb);
  }
  memcpy(res, c + len, (len + len - len) * sizeof (uint64_t));
  uint64_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t *tmp = alloca(len * sizeof (uint64_t));
  memset(tmp, 0U, len * sizeof (uint64_t));
  uint64_t c1 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
  for (uint32_t i = len / (uint32_t)4U * (uint32_t)4U; i < len; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    uint64_t *res_i = tmp + i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, res_i);
  }
  uint64_t c10 = c1;
  uint64_t c2 = c00 - c10;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

void
Hacl_Bignum_Montgomery_bn_to_mont_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv,
  uint64_t *r2,
  uint64_t *a,
  uint64_t *aM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t *c = alloca((len + len) * sizeof (uint64_t));
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t *tmp = alloca((uint32_t)4U * len * sizeof (uint64_t));
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, a, r2, tmp, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, nInv, c, aM);
}

void
Hacl_Bignum_Montgomery_bn_from_mont_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *a
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t *tmp = alloca((len + len) * sizeof (uint64_t));
  memset(tmp, 0U, (len + len) * sizeof (uint64_t));
  memcpy(tmp, aM, len * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, nInv_u64, tmp, a);
}

void
Hacl_Bignum_Montgomery_bn_mont_mul_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t *c = alloca((len + len) * sizeof (uint64_t));
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t *tmp = alloca((uint32_t)4U * len * sizeof (uint64_t));
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, aM, bM, tmp, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, nInv_u64, c, resM);
}

void
Hacl_Bignum_Montgomery_bn_mont_sqr_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t *c = alloca((len + len) * sizeof (uint64_t));
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t *tmp = alloca((uint32_t)4U * len * sizeof (uint64_t));
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len, aM, tmp, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, nInv_u64, c, resM);
}

static void
bn_almost_mont_reduction_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv,
  uint32_t *c,
  uint32_t *res
)
{
  uint32_t c0 = (uint32_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
  {
    uint32_t qj = nInv * c[i0];
    uint32_t *res_j0 = c + i0;
    uint32_t c1 = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint32_t a_i = n[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    for (uint32_t i = len / (uint32_t)4U * (uint32_t)4U; i < len; i++)
    {
      uint32_t a_i = n[i];
      uint32_t *res_i = res_j0 + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + len + i0;
    uint32_t res_j = c[len + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  memcpy(res, c + len, (len + len - len) * sizeof (uint32_t));
  uint32_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *tmp = alloca(len * sizeof (uint32_t));
  memset(tmp, 0U, len * sizeof (uint32_t));
  uint32_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len, res, n, tmp);
  (void)c1;
  uint32_t m = (uint32_t)0U - c00;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint32_t *os = res;
    uint32_t x = (m & tmp[i]) | (~m & res[i]);
    os[i] = x;
  }
}

static void
bn_almost_mont_mul_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv_u64,
  uint32_t *aM,
  uint32_t *bM,
  uint32_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t *c = alloca((len + len) * sizeof (uint32_t));
  memset(c, 0U, (len + len) * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * len);
  uint32_t *tmp = alloca((uint32_t)4U * len * sizeof (uint32_t));
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint32_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len, aM, bM, tmp, c);
  bn_almost_mont_reduction_u32(len, n, nInv_u64, c, resM);
}

static void
bn_almost_mont_sqr_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv_u64,
  uint32_t *aM,
  uint32_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t *c = alloca((len + len) * sizeof (uint32_t));
  memset(c, 0U, (len + len) * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * len);
  uint32_t *tmp = alloca((uint32_t)4U * len * sizeof (uint32_t));
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint32_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(len, aM, tmp, c);
  bn_almost_mont_reduction_u32(len, n, nInv_u64, c, resM);
}

static void
bn_almost_mont_reduction_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv,
  uint64_t *c,
  uint64_t *res
)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
  {
    uint64_t qj = nInv * c[i0];
    uint64_t *res_j0 = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
    for (uint32_t i = len / (uint32_t)4U * (uint32_t)4U; i < len; i++)
    {
      uint64_t a_i = n[i];
      uint64_t *res_i = res_j0 + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i);
    }
    uint64_t r = c1;
    uint64_t c10 = r;
    uint64_t *resb = c + len + i0;
    uint64_t res_j = c[len + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c10, res_j, resb);
  }
  memcpy(res, c + len, (len + len - len) * sizeof (uint64_t));
  uint64_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t *tmp = alloca(len * sizeof (uint64_t));
  memset(tmp, 0U, len * sizeof (uint64_t));
  uint64_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len, res, n, tmp);
  (void)c1;
  uint64_t m = (uint64_t)0U - c00;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t *os = res;
    uint64_t x = (m & tmp[i]) | (~m & res[i]);
    os[i] = x;
  }
}

static void
bn_almost_mont_mul_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t *c = alloca((len + len) * sizeof (uint64_t));
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t *tmp = alloca((uint32_t)4U * len * sizeof (uint64_t));
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, aM, bM, tmp, c);
  bn_almost_mont_reduction_u64(len, n, nInv_u64, c, resM);
}

static void
bn_almost_mont_sqr_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t *c = alloca((len + len) * sizeof (uint64_t));
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t *tmp = alloca((uint32_t)4U * len * sizeof (uint64_t));
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len, aM, tmp, c);
  bn_almost_mont_reduction_u64(len, n, nInv_u64, c, resM);
}

uint32_t
Hacl_Bignum_Exponentiation_bn_check_mod_exp_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *one = alloca(len * sizeof (uint32_t));
  memset(one, 0U, len * sizeof (uint32_t));
  memset(one, 0U, len * sizeof (uint32_t));
  one[0U] = (uint32_t)1U;
  uint32_t bit0 = n[0U] & (uint32_t)1U;
  uint32_t m0 = (uint32_t)0U - bit0;
  uint32_t acc0 = (uint32_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[i], n[i]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  uint32_t m10 = acc0;
  uint32_t m00 = m0 & m10;
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)32U + (uint32_t)1U;
  }
  uint32_t m1;
  if (bBits < (uint32_t)32U * bLen)
  {
    KRML_CHECK_SIZE(sizeof (uint32_t), bLen);
    uint32_t *b2 = alloca(bLen * sizeof (uint32_t));
    memset(b2, 0U, bLen * sizeof (uint32_t));
    uint32_t i0 = bBits / (uint32_t)32U;
    uint32_t j = bBits % (uint32_t)32U;
    b2[i0] = b2[i0] | (uint32_t)1U << j;
    uint32_t acc = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < bLen; i++)
    {
      uint32_t beq = FStar_UInt32_eq_mask(b[i], b2[i]);
      uint32_t blt = ~FStar_UInt32_gte_mask(b[i], b2[i]);
      acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
    }
    uint32_t res = acc;
    m1 = res;
  }
  else
  {
    m1 = (uint32_t)0xFFFFFFFFU;
  }
  uint32_t acc = (uint32_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
  }
  uint32_t m2 = acc;
  uint32_t m = m1 & m2;
  return m00 & m;
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t mu,
  uint32_t *r2,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  if (bBits < (uint32_t)200U)
  {
    KRML_CHECK_SIZE(sizeof (uint32_t), len);
    uint32_t *aM = alloca(len * sizeof (uint32_t));
    memset(aM, 0U, len * sizeof (uint32_t));
    KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
    uint32_t *c = alloca((len + len) * sizeof (uint32_t));
    memset(c, 0U, (len + len) * sizeof (uint32_t));
    KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * len);
    uint32_t *tmp0 = alloca((uint32_t)4U * len * sizeof (uint32_t));
    memset(tmp0, 0U, (uint32_t)4U * len * sizeof (uint32_t));
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len, a, r2, tmp0, c);
    Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, mu, c, aM);
    KRML_CHECK_SIZE(sizeof (uint32_t), len);
    uint32_t *resM = alloca(len * sizeof (uint32_t));
    memset(resM, 0U, len * sizeof (uint32_t));
    KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
    uint32_t *tmp1 = alloca((len + len) * sizeof (uint32_t));
    memset(tmp1, 0U, (len + len) * sizeof (uint32_t));
    memcpy(tmp1, r2, len * sizeof (uint32_t));
    Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, mu, tmp1, resM);
    for (uint32_t i = (uint32_t)0U; i < bBits; i++)
    {
      uint32_t i1 = i / (uint32_t)32U;
      uint32_t j = i % (uint32_t)32U;
      uint32_t tmp = b[i1];
      uint32_t bit = tmp >> j & (uint32_t)1U;
      if (!(bit == (uint32_t)0U))
      {
        bn_almost_mont_mul_u32(len, n, mu, resM, aM, resM);
      }
      bn_almost_mont_sqr_u32(len, n, mu, aM, aM);
    }
    KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
    uint32_t *tmp = alloca((len + len) * sizeof (uint32_t));
    memset(tmp, 0U, (len + len) * sizeof (uint32_t));
    memcpy(tmp, resM, len * sizeof (uint32_t));
    Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, mu, tmp, res);
    return;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *aM = alloca(len * sizeof (uint32_t));
  memset(aM, 0U, len * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t *c = alloca((len + len) * sizeof (uint32_t));
  memset(c, 0U, (len + len) * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * len);
  uint32_t *tmp0 = alloca((uint32_t)4U * len * sizeof (uint32_t));
  memset(tmp0, 0U, (uint32_t)4U * len * sizeof (uint32_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len, a, r2, tmp0, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, mu, c, aM);
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *resM = alloca(len * sizeof (uint32_t));
  memset(resM, 0U, len * sizeof (uint32_t));
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)32U + (uint32_t)1U;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t *tmp = alloca((len + len) * sizeof (uint32_t));
  memset(tmp, 0U, (len + len) * sizeof (uint32_t));
  memcpy(tmp, r2, len * sizeof (uint32_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, mu, tmp, resM);
  uint32_t table_len = (uint32_t)16U;
  KRML_CHECK_SIZE(sizeof (uint32_t), table_len * len);
  uint32_t *table = alloca(table_len * len * sizeof (uint32_t));
  memset(table, 0U, table_len * len * sizeof (uint32_t));
  memcpy(table, resM, len * sizeof (uint32_t));
  uint32_t *t1 = table + len;
  memcpy(t1, aM, len * sizeof (uint32_t));
  for (uint32_t i = (uint32_t)0U; i < table_len - (uint32_t)2U; i++)
  {
    uint32_t *t11 = table + (i + (uint32_t)1U) * len;
    uint32_t *t2 = table + (i + (uint32_t)2U) * len;
    bn_almost_mont_mul_u32(len, n, mu, t11, aM, t2);
  }
  for (uint32_t i = (uint32_t)0U; i < bBits / (uint32_t)4U; i++)
  {
    for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
    {
      bn_almost_mont_sqr_u32(len, n, mu, resM, resM);
    }
    uint32_t mask_l = (uint32_t)16U - (uint32_t)1U;
    uint32_t i1 = (bBits - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)32U;
    uint32_t j = (bBits - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)32U;
    uint32_t p1 = b[i1] >> j;
    uint32_t ite;
    if (i1 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)32U - j);
    }
    else
    {
      ite = p1;
    }
    uint32_t bits_l = ite & mask_l;
    uint32_t bits_l32 = bits_l;
    uint32_t *a_bits_l = table + bits_l32 * len;
    bn_almost_mont_mul_u32(len, n, mu, resM, a_bits_l, resM);
  }
  if (!(bBits % (uint32_t)4U == (uint32_t)0U))
  {
    uint32_t c0 = bBits % (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < c0; i++)
    {
      bn_almost_mont_sqr_u32(len, n, mu, resM, resM);
    }
    uint32_t c1 = bBits % (uint32_t)4U;
    uint32_t mask_l = ((uint32_t)1U << c1) - (uint32_t)1U;
    uint32_t i = (uint32_t)0U;
    uint32_t j = (uint32_t)0U;
    uint32_t p1 = b[i] >> j;
    uint32_t ite;
    if (i + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i + (uint32_t)1U] << ((uint32_t)32U - j);
    }
    else
    {
      ite = p1;
    }
    uint32_t bits_c = ite & mask_l;
    uint32_t bits_c0 = bits_c;
    uint32_t bits_c32 = bits_c0;
    uint32_t *a_bits_c = table + bits_c32 * len;
    bn_almost_mont_mul_u32(len, n, mu, resM, a_bits_c, resM);
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t *tmp1 = alloca((len + len) * sizeof (uint32_t));
  memset(tmp1, 0U, (len + len) * sizeof (uint32_t));
  memcpy(tmp1, resM, len * sizeof (uint32_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, mu, tmp1, res);
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t mu,
  uint32_t *r2,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  if (bBits < (uint32_t)200U)
  {
    KRML_CHECK_SIZE(sizeof (uint32_t), len);
    uint32_t *aM = alloca(len * sizeof (uint32_t));
    memset(aM, 0U, len * sizeof (uint32_t));
    KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
    uint32_t *c = alloca((len + len) * sizeof (uint32_t));
    memset(c, 0U, (len + len) * sizeof (uint32_t));
    KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * len);
    uint32_t *tmp0 = alloca((uint32_t)4U * len * sizeof (uint32_t));
    memset(tmp0, 0U, (uint32_t)4U * len * sizeof (uint32_t));
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len, a, r2, tmp0, c);
    Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, mu, c, aM);
    KRML_CHECK_SIZE(sizeof (uint32_t), len);
    uint32_t *resM = alloca(len * sizeof (uint32_t));
    memset(resM, 0U, len * sizeof (uint32_t));
    KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
    uint32_t *tmp1 = alloca((len + len) * sizeof (uint32_t));
    memset(tmp1, 0U, (len + len) * sizeof (uint32_t));
    memcpy(tmp1, r2, len * sizeof (uint32_t));
    Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, mu, tmp1, resM);
    uint32_t sw = (uint32_t)0U;
    for (uint32_t i0 = (uint32_t)0U; i0 < bBits; i0++)
    {
      uint32_t i1 = (bBits - i0 - (uint32_t)1U) / (uint32_t)32U;
      uint32_t j = (bBits - i0 - (uint32_t)1U) % (uint32_t)32U;
      uint32_t tmp = b[i1];
      uint32_t bit = tmp >> j & (uint32_t)1U;
      uint32_t sw1 = bit ^ sw;
      for (uint32_t i = (uint32_t)0U; i < len; i++)
      {
        uint32_t dummy = ((uint32_t)0U - sw1) & (resM[i] ^ aM[i]);
        resM[i] = resM[i] ^ dummy;
        aM[i] = aM[i] ^ dummy;
      }
      bn_almost_mont_mul_u32(len, n, mu, aM, resM, aM);
      bn_almost_mont_sqr_u32(len, n, mu, resM, resM);
      sw = bit;
    }
    uint32_t sw0 = sw;
    for (uint32_t i = (uint32_t)0U; i < len; i++)
    {
      uint32_t dummy = ((uint32_t)0U - sw0) & (resM[i] ^ aM[i]);
      resM[i] = resM[i] ^ dummy;
      aM[i] = aM[i] ^ dummy;
    }
    KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
    uint32_t *tmp = alloca((len + len) * sizeof (uint32_t));
    memset(tmp, 0U, (len + len) * sizeof (uint32_t));
    memcpy(tmp, resM, len * sizeof (uint32_t));
    Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, mu, tmp, res);
    return;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *aM = alloca(len * sizeof (uint32_t));
  memset(aM, 0U, len * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t *c0 = alloca((len + len) * sizeof (uint32_t));
  memset(c0, 0U, (len + len) * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * len);
  uint32_t *tmp0 = alloca((uint32_t)4U * len * sizeof (uint32_t));
  memset(tmp0, 0U, (uint32_t)4U * len * sizeof (uint32_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len, a, r2, tmp0, c0);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, mu, c0, aM);
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *resM = alloca(len * sizeof (uint32_t));
  memset(resM, 0U, len * sizeof (uint32_t));
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)32U + (uint32_t)1U;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t *tmp = alloca((len + len) * sizeof (uint32_t));
  memset(tmp, 0U, (len + len) * sizeof (uint32_t));
  memcpy(tmp, r2, len * sizeof (uint32_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, mu, tmp, resM);
  uint32_t table_len = (uint32_t)16U;
  KRML_CHECK_SIZE(sizeof (uint32_t), table_len * len);
  uint32_t *table = alloca(table_len * len * sizeof (uint32_t));
  memset(table, 0U, table_len * len * sizeof (uint32_t));
  memcpy(table, resM, len * sizeof (uint32_t));
  uint32_t *t1 = table + len;
  memcpy(t1, aM, len * sizeof (uint32_t));
  for (uint32_t i = (uint32_t)0U; i < table_len - (uint32_t)2U; i++)
  {
    uint32_t *t11 = table + (i + (uint32_t)1U) * len;
    uint32_t *t2 = table + (i + (uint32_t)2U) * len;
    bn_almost_mont_mul_u32(len, n, mu, t11, aM, t2);
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < bBits / (uint32_t)4U; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      bn_almost_mont_sqr_u32(len, n, mu, resM, resM);
    }
    uint32_t mask_l = (uint32_t)16U - (uint32_t)1U;
    uint32_t i1 = (bBits - (uint32_t)4U * i0 - (uint32_t)4U) / (uint32_t)32U;
    uint32_t j = (bBits - (uint32_t)4U * i0 - (uint32_t)4U) % (uint32_t)32U;
    uint32_t p1 = b[i1] >> j;
    uint32_t ite;
    if (i1 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)32U - j);
    }
    else
    {
      ite = p1;
    }
    uint32_t bits_l = ite & mask_l;
    KRML_CHECK_SIZE(sizeof (uint32_t), len);
    uint32_t *a_bits_l = alloca(len * sizeof (uint32_t));
    memset(a_bits_l, 0U, len * sizeof (uint32_t));
    memcpy(a_bits_l, table, len * sizeof (uint32_t));
    for (uint32_t i2 = (uint32_t)0U; i2 < table_len - (uint32_t)1U; i2++)
    {
      uint32_t c = FStar_UInt32_eq_mask(bits_l, i2 + (uint32_t)1U);
      uint32_t *res_j = table + (i2 + (uint32_t)1U) * len;
      for (uint32_t i = (uint32_t)0U; i < len; i++)
      {
        uint32_t *os = a_bits_l;
        uint32_t x = (c & res_j[i]) | (~c & a_bits_l[i]);
        os[i] = x;
      }
    }
    bn_almost_mont_mul_u32(len, n, mu, resM, a_bits_l, resM);
  }
  if (!(bBits % (uint32_t)4U == (uint32_t)0U))
  {
    uint32_t c = bBits % (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < c; i++)
    {
      bn_almost_mont_sqr_u32(len, n, mu, resM, resM);
    }
    uint32_t c10 = bBits % (uint32_t)4U;
    uint32_t mask_l = ((uint32_t)1U << c10) - (uint32_t)1U;
    uint32_t i0 = (uint32_t)0U;
    uint32_t j = (uint32_t)0U;
    uint32_t p1 = b[i0] >> j;
    uint32_t ite;
    if (i0 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i0 + (uint32_t)1U] << ((uint32_t)32U - j);
    }
    else
    {
      ite = p1;
    }
    uint32_t bits_c = ite & mask_l;
    uint32_t bits_c0 = bits_c;
    KRML_CHECK_SIZE(sizeof (uint32_t), len);
    uint32_t *a_bits_c = alloca(len * sizeof (uint32_t));
    memset(a_bits_c, 0U, len * sizeof (uint32_t));
    memcpy(a_bits_c, table, len * sizeof (uint32_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < table_len - (uint32_t)1U; i1++)
    {
      uint32_t c1 = FStar_UInt32_eq_mask(bits_c0, i1 + (uint32_t)1U);
      uint32_t *res_j = table + (i1 + (uint32_t)1U) * len;
      for (uint32_t i = (uint32_t)0U; i < len; i++)
      {
        uint32_t *os = a_bits_c;
        uint32_t x = (c1 & res_j[i]) | (~c1 & a_bits_c[i]);
        os[i] = x;
      }
    }
    bn_almost_mont_mul_u32(len, n, mu, resM, a_bits_c, resM);
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t *tmp1 = alloca((len + len) * sizeof (uint32_t));
  memset(tmp1, 0U, (len + len) * sizeof (uint32_t));
  memcpy(tmp1, resM, len * sizeof (uint32_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u32(len, n, mu, tmp1, res);
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u32(
  uint32_t len,
  uint32_t nBits,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *r2 = alloca(len * sizeof (uint32_t));
  memset(r2, 0U, len * sizeof (uint32_t));
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32(len, nBits, n, r2);
  uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
  Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32(len, n, mu, r2, a, bBits, b, res);
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u32(
  uint32_t len,
  uint32_t nBits,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *r2 = alloca(len * sizeof (uint32_t));
  memset(r2, 0U, len * sizeof (uint32_t));
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32(len, nBits, n, r2);
  uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
  Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u32(len, n, mu, r2, a, bBits, b, res);
}

uint64_t
Hacl_Bignum_Exponentiation_bn_check_mod_exp_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t *one = alloca(len * sizeof (uint64_t));
  memset(one, 0U, len * sizeof (uint64_t));
  memset(one, 0U, len * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint64_t bit0 = n[0U] & (uint64_t)1U;
  uint64_t m0 = (uint64_t)0U - bit0;
  uint64_t acc0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
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
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(a[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t m2 = acc;
  uint64_t m = m1 & m2;
  return m00 & m;
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64(
  uint32_t len,
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
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t *aM = alloca(len * sizeof (uint64_t));
    memset(aM, 0U, len * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
    uint64_t *c = alloca((len + len) * sizeof (uint64_t));
    memset(c, 0U, (len + len) * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
    uint64_t *tmp0 = alloca((uint32_t)4U * len * sizeof (uint64_t));
    memset(tmp0, 0U, (uint32_t)4U * len * sizeof (uint64_t));
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, a, r2, tmp0, c);
    Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, mu, c, aM);
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t *resM = alloca(len * sizeof (uint64_t));
    memset(resM, 0U, len * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
    uint64_t *tmp1 = alloca((len + len) * sizeof (uint64_t));
    memset(tmp1, 0U, (len + len) * sizeof (uint64_t));
    memcpy(tmp1, r2, len * sizeof (uint64_t));
    Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, mu, tmp1, resM);
    for (uint32_t i = (uint32_t)0U; i < bBits; i++)
    {
      uint32_t i1 = i / (uint32_t)64U;
      uint32_t j = i % (uint32_t)64U;
      uint64_t tmp = b[i1];
      uint64_t bit = tmp >> j & (uint64_t)1U;
      if (!(bit == (uint64_t)0U))
      {
        bn_almost_mont_mul_u64(len, n, mu, resM, aM, resM);
      }
      bn_almost_mont_sqr_u64(len, n, mu, aM, aM);
    }
    KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
    uint64_t *tmp = alloca((len + len) * sizeof (uint64_t));
    memset(tmp, 0U, (len + len) * sizeof (uint64_t));
    memcpy(tmp, resM, len * sizeof (uint64_t));
    Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, mu, tmp, res);
    return;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t *aM = alloca(len * sizeof (uint64_t));
  memset(aM, 0U, len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t *c = alloca((len + len) * sizeof (uint64_t));
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t *tmp0 = alloca((uint32_t)4U * len * sizeof (uint64_t));
  memset(tmp0, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, a, r2, tmp0, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, mu, c, aM);
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t *resM = alloca(len * sizeof (uint64_t));
  memset(resM, 0U, len * sizeof (uint64_t));
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t *tmp = alloca((len + len) * sizeof (uint64_t));
  memset(tmp, 0U, (len + len) * sizeof (uint64_t));
  memcpy(tmp, r2, len * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, mu, tmp, resM);
  uint32_t table_len = (uint32_t)16U;
  KRML_CHECK_SIZE(sizeof (uint64_t), table_len * len);
  uint64_t *table = alloca(table_len * len * sizeof (uint64_t));
  memset(table, 0U, table_len * len * sizeof (uint64_t));
  memcpy(table, resM, len * sizeof (uint64_t));
  uint64_t *t1 = table + len;
  memcpy(t1, aM, len * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < table_len - (uint32_t)2U; i++)
  {
    uint64_t *t11 = table + (i + (uint32_t)1U) * len;
    uint64_t *t2 = table + (i + (uint32_t)2U) * len;
    bn_almost_mont_mul_u64(len, n, mu, t11, aM, t2);
  }
  for (uint32_t i = (uint32_t)0U; i < bBits / (uint32_t)4U; i++)
  {
    for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
    {
      bn_almost_mont_sqr_u64(len, n, mu, resM, resM);
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
    uint64_t *a_bits_l = table + bits_l32 * len;
    bn_almost_mont_mul_u64(len, n, mu, resM, a_bits_l, resM);
  }
  if (!(bBits % (uint32_t)4U == (uint32_t)0U))
  {
    uint32_t c0 = bBits % (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < c0; i++)
    {
      bn_almost_mont_sqr_u64(len, n, mu, resM, resM);
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
    uint64_t *a_bits_c = table + bits_c32 * len;
    bn_almost_mont_mul_u64(len, n, mu, resM, a_bits_c, resM);
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t *tmp1 = alloca((len + len) * sizeof (uint64_t));
  memset(tmp1, 0U, (len + len) * sizeof (uint64_t));
  memcpy(tmp1, resM, len * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, mu, tmp1, res);
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64(
  uint32_t len,
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
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t *aM = alloca(len * sizeof (uint64_t));
    memset(aM, 0U, len * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
    uint64_t *c = alloca((len + len) * sizeof (uint64_t));
    memset(c, 0U, (len + len) * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
    uint64_t *tmp0 = alloca((uint32_t)4U * len * sizeof (uint64_t));
    memset(tmp0, 0U, (uint32_t)4U * len * sizeof (uint64_t));
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, a, r2, tmp0, c);
    Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, mu, c, aM);
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t *resM = alloca(len * sizeof (uint64_t));
    memset(resM, 0U, len * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
    uint64_t *tmp1 = alloca((len + len) * sizeof (uint64_t));
    memset(tmp1, 0U, (len + len) * sizeof (uint64_t));
    memcpy(tmp1, r2, len * sizeof (uint64_t));
    Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, mu, tmp1, resM);
    uint64_t sw = (uint64_t)0U;
    for (uint32_t i0 = (uint32_t)0U; i0 < bBits; i0++)
    {
      uint32_t i1 = (bBits - i0 - (uint32_t)1U) / (uint32_t)64U;
      uint32_t j = (bBits - i0 - (uint32_t)1U) % (uint32_t)64U;
      uint64_t tmp = b[i1];
      uint64_t bit = tmp >> j & (uint64_t)1U;
      uint64_t sw1 = bit ^ sw;
      for (uint32_t i = (uint32_t)0U; i < len; i++)
      {
        uint64_t dummy = ((uint64_t)0U - sw1) & (resM[i] ^ aM[i]);
        resM[i] = resM[i] ^ dummy;
        aM[i] = aM[i] ^ dummy;
      }
      bn_almost_mont_mul_u64(len, n, mu, aM, resM, aM);
      bn_almost_mont_sqr_u64(len, n, mu, resM, resM);
      sw = bit;
    }
    uint64_t sw0 = sw;
    for (uint32_t i = (uint32_t)0U; i < len; i++)
    {
      uint64_t dummy = ((uint64_t)0U - sw0) & (resM[i] ^ aM[i]);
      resM[i] = resM[i] ^ dummy;
      aM[i] = aM[i] ^ dummy;
    }
    KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
    uint64_t *tmp = alloca((len + len) * sizeof (uint64_t));
    memset(tmp, 0U, (len + len) * sizeof (uint64_t));
    memcpy(tmp, resM, len * sizeof (uint64_t));
    Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, mu, tmp, res);
    return;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t *aM = alloca(len * sizeof (uint64_t));
  memset(aM, 0U, len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t *c0 = alloca((len + len) * sizeof (uint64_t));
  memset(c0, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t *tmp0 = alloca((uint32_t)4U * len * sizeof (uint64_t));
  memset(tmp0, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, a, r2, tmp0, c0);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, mu, c0, aM);
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t *resM = alloca(len * sizeof (uint64_t));
  memset(resM, 0U, len * sizeof (uint64_t));
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t *tmp = alloca((len + len) * sizeof (uint64_t));
  memset(tmp, 0U, (len + len) * sizeof (uint64_t));
  memcpy(tmp, r2, len * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, mu, tmp, resM);
  uint32_t table_len = (uint32_t)16U;
  KRML_CHECK_SIZE(sizeof (uint64_t), table_len * len);
  uint64_t *table = alloca(table_len * len * sizeof (uint64_t));
  memset(table, 0U, table_len * len * sizeof (uint64_t));
  memcpy(table, resM, len * sizeof (uint64_t));
  uint64_t *t1 = table + len;
  memcpy(t1, aM, len * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < table_len - (uint32_t)2U; i++)
  {
    uint64_t *t11 = table + (i + (uint32_t)1U) * len;
    uint64_t *t2 = table + (i + (uint32_t)2U) * len;
    bn_almost_mont_mul_u64(len, n, mu, t11, aM, t2);
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < bBits / (uint32_t)4U; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      bn_almost_mont_sqr_u64(len, n, mu, resM, resM);
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
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t *a_bits_l = alloca(len * sizeof (uint64_t));
    memset(a_bits_l, 0U, len * sizeof (uint64_t));
    memcpy(a_bits_l, table, len * sizeof (uint64_t));
    for (uint32_t i2 = (uint32_t)0U; i2 < table_len - (uint32_t)1U; i2++)
    {
      uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i2 + (uint32_t)1U));
      uint64_t *res_j = table + (i2 + (uint32_t)1U) * len;
      for (uint32_t i = (uint32_t)0U; i < len; i++)
      {
        uint64_t *os = a_bits_l;
        uint64_t x = (c & res_j[i]) | (~c & a_bits_l[i]);
        os[i] = x;
      }
    }
    bn_almost_mont_mul_u64(len, n, mu, resM, a_bits_l, resM);
  }
  if (!(bBits % (uint32_t)4U == (uint32_t)0U))
  {
    uint32_t c = bBits % (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < c; i++)
    {
      bn_almost_mont_sqr_u64(len, n, mu, resM, resM);
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
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t *a_bits_c = alloca(len * sizeof (uint64_t));
    memset(a_bits_c, 0U, len * sizeof (uint64_t));
    memcpy(a_bits_c, table, len * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < table_len - (uint32_t)1U; i1++)
    {
      uint64_t c1 = FStar_UInt64_eq_mask(bits_c0, (uint64_t)(i1 + (uint32_t)1U));
      uint64_t *res_j = table + (i1 + (uint32_t)1U) * len;
      for (uint32_t i = (uint32_t)0U; i < len; i++)
      {
        uint64_t *os = a_bits_c;
        uint64_t x = (c1 & res_j[i]) | (~c1 & a_bits_c[i]);
        os[i] = x;
      }
    }
    bn_almost_mont_mul_u64(len, n, mu, resM, a_bits_c, resM);
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t *tmp1 = alloca((len + len) * sizeof (uint64_t));
  memset(tmp1, 0U, (len + len) * sizeof (uint64_t));
  memcpy(tmp1, resM, len * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(len, n, mu, tmp1, res);
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u64(
  uint32_t len,
  uint32_t nBits,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t *r2 = alloca(len * sizeof (uint64_t));
  memset(r2, 0U, len * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(len, nBits, n, r2);
  uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64(len, n, mu, r2, a, bBits, b, res);
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u64(
  uint32_t len,
  uint32_t nBits,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t *r2 = alloca(len * sizeof (uint64_t));
  memset(r2, 0U, len * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(len, nBits, n, r2);
  uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64(len, n, mu, r2, a, bBits, b, res);
}

